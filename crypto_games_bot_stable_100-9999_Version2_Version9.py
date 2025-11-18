#!/usr/bin/env python3
# Crypto.Games multi-bot GUI — multithreaded UI queue
# Дополнения:
# - Независимая база банка для Cover 50% (cover_base_bank).
# - Авто Cover 50% при выигрыше в диапазоне payout 5..100 (2 авто спина).
# - Учёт прибыли Cover 50%, счётчики Cover 50% выигрышей/проигрышей.
# - Логирование результата каждого спина с Roll и WIN/LOSS, цветные строки в UI.
# - Авто-сброс cover_base_bank при достижении заданной глобальной прибыли profit_global >= TargetProfit.
#
# WARNING: Реальные ставки при вводе реального API ключа.

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
import threading
import time
import random
import string
import requests
import os
import traceback
import queue
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from decimal import Decimal, getcontext, ROUND_DOWN, InvalidOperation

getcontext().prec = 40

API_BASE = "https://api.crypto.games/v1"
MAX_COVER_PAYOUT = Decimal("9999")

@dataclass
class BetConfig:
    coin: str = "USDT"
    api_key: str = ""
    base_bet: Decimal = Decimal("0.001")
    min_bet_enforced: Decimal = Decimal("0.001")
    max_bet_limit: Decimal = Decimal("1.0")
    speed_ms: int = 50
    min_bet_refresh_secs: int = 30
    target_min_bets_on_win: int = 10

MIN_API_CHANCE = Decimal("0.01")
MAX_API_CHANCE = Decimal("9920")

class APIClient:
    def __init__(self, api_base: str = API_BASE, timeout: int = 15):
        self.base = api_base.rstrip("/")
        self.timeout = timeout
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": "CryptoGamesBot/1.0",
            "Content-Type": "application/json",
            "Accept": "application/json",
        })

    def _get(self, path: str):
        url = f"{self.base}{path}"
        try:
            r = self.session.get(url, timeout=self.timeout)
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            try: return {"error": r.json()}
            except Exception: return {"error": str(e)}

    def _post(self, path: str, payload: dict):
        url = f"{self.base}{path}"
        try:
            r = self.session.post(url, json=payload, timeout=self.timeout)
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            try: return {"error": r.json()}
            except Exception: return {"error": str(e)}

    def settings(self, coin: str):
        return self._get(f"/settings/{coin}")

    def balance(self, coin: str, key: str):
        return self._get(f"/balance/{coin}/{key}")

    def user(self, coin: str, key: str):
        return self._get(f"/user/{coin}/{key}")

    def placebet(self, coin: str, key: str, bet_amount, payout, underover_bool, client_seed):
        payload = {"Bet": float(bet_amount), "Payout": float(payout), "UnderOver": bool(underover_bool), "ClientSeed": client_seed}
        return self._post(f"/placebet/{coin}/{key}", payload)

    def generate_client_seed(self) -> str:
        return ''.join(random.choice(string.ascii_letters + string.digits) for _ in range(16))

def quantize_bet(bet: Decimal, max_scale=8):
    q = Decimal(1).scaleb(-max_scale)
    try: return bet.quantize(q, rounding=ROUND_DOWN)
    except Exception: return bet

def safe_decimal(val, default="0"):
    if val is None: return Decimal(default)
    try: return Decimal(str(val))
    except Exception: return Decimal(default)

def compute_covering_bet_for_target(payout: Decimal, profit_target: Decimal,
                                    min_bet: Decimal, max_bet_limit, current_bank):
    try: payout = Decimal(payout)
    except Exception: payout = Decimal("2")
    denom = payout - Decimal("1")
    if denom <= 0:
        return quantize_bet(Decimal(min_bet or Decimal("0.00000001")))
    bet = quantize_bet(Decimal(profit_target) / denom)
    if max_bet_limit is not None:
        try:
            mb = Decimal(str(max_bet_limit))
            if bet > mb: bet = mb
        except Exception: pass
    if current_bank is not None:
        try:
            cb = Decimal(str(current_bank))
            if bet > cb: bet = cb
        except Exception: pass
    if bet <= Decimal("0"): bet = Decimal("0.00000001")
    return quantize_bet(bet)

class LinearPayoutStrategy:
    def __init__(self, start_payout=Decimal("100"), max_payout=MAX_COVER_PAYOUT):
        self.start_payout = Decimal(start_payout)
        self.max_payout = Decimal(max_payout)
        self.current_payout = Decimal(start_payout)
    def reset(self):
        self.current_payout = Decimal(self.start_payout)
    def next_payout_and_bet(self, state):
        payout = self.current_payout
        nxt = payout + Decimal(1)
        if nxt > self.max_payout: nxt = Decimal(self.start_payout)
        self.current_payout = nxt
        bet = Decimal(state.get("min_bet", Decimal("0.001"))) or Decimal("0.001")
        return payout, bet, 1, False

class CryptoGamesBot:
    def __init__(self, bot_id: str, api: APIClient, config: BetConfig,
                 log_cb, bank_cb, stats_cb, ui_callbacks=None,
                 pause_on_fail=False, stop_on_win=False,
                 executor: ThreadPoolExecutor = None):
        self.bot_id = bot_id
        self.api = api
        self.config = config
        self.log_cb = log_cb
        self.bank_cb = bank_cb
        self.stats_cb = stats_cb
        self.ui_callbacks = ui_callbacks or {}
        self.is_running = False
        self.paused = False
        self.client_seed = self.api.generate_client_seed()
        self.reset_stats()
        self.initial_bank = None
        self.last_successful_bank = None
        self.profit_global = Decimal("0")
        self.min_bet = Decimal("0")
        self._last_min_bet_fetch = 0.0
        self.strategy = None
        self.strategy_factories = []
        self.start_base_bet = Decimal(self.config.base_bet)
        self.pause_on_fail = pause_on_fail
        self.stop_on_win = stop_on_win
        self.local_nonce = 0
        self.executor = executor
        self.payout_wraps = 0
        self._prev_payout = None
        self.manager_ref = None

        # Cover 50%
        self.cover50_pending = False
        self.cover50_cap_ratio = Decimal("0.02")
        self.cover50_auto_remaining = 0
        self.auto_cover_payout = None
        self.auto_trigger_min = Decimal("5")
        self.auto_trigger_max = Decimal("100")

        # Cover 50% прибыль и счётчики
        self.cover50_profit_total = Decimal("0")
        self.cover50_profit_manual = Decimal("0")
        self.cover50_profit_auto = Decimal("0")
        self.cover50_wins_total = 0
        self.cover50_wins_manual = 0
        self.cover50_wins_auto = 0
        self.cover50_losses_total = 0

        # База для Cover 50%
        self.cover_base_bank = None

        # Авто-сброс базы по прибыли
        self.auto_reset_profit_enabled = False
        self.auto_reset_profit_threshold = Decimal("1.0")  # по умолчанию
        self.auto_reset_profit_triggered = False  # чтобы не дёргать много раз

    def pause_toggle(self):
        self.paused = not self.paused
        return self.paused

    def set_strategy(self, strategy_obj):
        self.strategy = strategy_obj
        try: self.strategy.reset()
        except Exception: pass

    def set_strategy_factories(self, factories):
        self.strategy_factories = list(factories)

    def reset_stats(self):
        self.stats = {"total_bets": 0, "wins": 0, "losses": 0, "profit": Decimal("0"),
                      "current_streak": 0, "total_wagered": Decimal("0"),
                      "max_loss_sum": Decimal("0"), "max_bet": Decimal("0"),
                      "strategy_resets": 0}
        self.loss_sum = Decimal("0")
        self.streak = 0
        self.spin_count = 0

    def restart_after_tp(self, new_initial: Decimal):
        self.initial_bank = safe_decimal(new_initial)
        self.last_successful_bank = self.initial_bank
        self.profit_global = Decimal("0")
        self.reset_stats()
        if self.strategy:
            try: self.strategy.reset()
            except: pass
        # не трогаем cover_base_bank
        self._log(f"[{self.bot_id}] ▶ TP restart: initial={self.initial_bank:.8f} (cover_base_bank={self.cover_base_bank})")

    def _log(self, msg):
        try: self.log_cb(msg)
        except Exception: print(f"[{self.bot_id}] {msg}")

    def get_current_balance(self):
        if not self.config.api_key: return Decimal("0")
        try:
            res = self.api.balance(self.config.coin, self.config.api_key)
            if isinstance(res, dict) and res.get("Balance") is not None:
                bal = safe_decimal(res.get("Balance"))
                self._push_bank_payload(bal)
                return bal
        except Exception: pass
        try:
            usr = self.api.user(self.config.coin, self.config.api_key)
            if isinstance(usr, dict) and usr.get("Balance") is not None:
                bal = safe_decimal(usr.get("Balance"))
                self._push_bank_payload(bal)
                return bal
        except Exception: pass
        return Decimal("0")

    def _push_bank_payload(self, bal: Decimal):
        if self.initial_bank is None: self.initial_bank = bal
        if self.cover_base_bank is None: self.cover_base_bank = bal
        data = {
            "initial_bank": self.initial_bank,
            "last_successful_bank": self.last_successful_bank if self.last_successful_bank is not None else self.initial_bank,
            "current_bank": bal,
            "profit_global": self.profit_global,
            "cover50_profit_total": self.cover50_profit_total,
            "cover50_profit_manual": self.cover50_profit_manual,
            "cover50_profit_auto": self.cover50_profit_auto,
            "cover50_wins_total": self.cover50_wins_total,
            "cover50_wins_manual": self.cover50_wins_manual,
            "cover50_wins_auto": self.cover50_wins_auto,
            "cover50_losses_total": self.cover50_losses_total,
            "cover_base_bank": self.cover_base_bank,
            "auto_reset_profit_threshold": self.auto_reset_profit_threshold,
            "auto_reset_profit_enabled": self.auto_reset_profit_enabled,
            "bot_id": self.bot_id
        }
        try: self.bank_cb(data)
        except: pass

    def _bank(self, balance: Decimal):
        self._push_bank_payload(balance)

    def _stats(self):
        s = {"total_bets": self.stats["total_bets"],
             "wins": self.stats["wins"],
             "losses": self.stats["losses"],
             "profit": float(self.stats["profit"]),
             "current_streak": self.stats["current_streak"],
             "total_wagered": float(self.stats["total_wagered"]),
             "strategy_resets": self.stats["strategy_resets"],
             "bot_id": self.bot_id}
        try: self.stats_cb(s)
        except: pass

    def fetch_settings_if_needed(self):
        now = time.time()
        if now - self._last_min_bet_fetch < self.config.min_bet_refresh_secs: return
        self._last_min_bet_fetch = now
        res = self.api.settings(self.config.coin)
        if isinstance(res, dict) and res.get("MinBet") is not None:
            try:
                self.min_bet = safe_decimal(res.get("MinBet"))
                self._log(f"[{self.bot_id}] MinBet={self.min_bet}")
            except Exception as e:
                self._log(f"[{self.bot_id}] Ошибка MinBet: {e}")

    def request_cover50(self, cap_ratio: Decimal | None):
        if cap_ratio is not None and cap_ratio > 0:
            self.cover50_cap_ratio = Decimal(cap_ratio)
        self.cover50_pending = True
        self._log(f"[{self.bot_id}] Cover50 manual (cap {self.cover50_cap_ratio*100:.2f}%) → next spin")

    def reset_cover_base(self, current_balance: Decimal):
        self.cover_base_bank = current_balance
        self._log(f"[{self.bot_id}] 🔄 Cover base reset → {self.cover_base_bank:.8f}")

    def _calc_cover_drawdown(self, current_balance: Decimal) -> Decimal:
        if self.cover_base_bank is None: return Decimal("0")
        dd = self.cover_base_bank - current_balance
        return dd if dd > 0 else Decimal("0")

    def _cover50_bet(self, payout: Decimal, current_balance: Decimal) -> Decimal | None:
        dd = self._calc_cover_drawdown(current_balance)
        if dd <= 0: return None
        target_profit = dd * Decimal("0.50")
        bet = compute_covering_bet_for_target(
            payout,
            target_profit,
            self.min_bet or Decimal("0.001"),
            self.config.max_bet_limit,
            current_balance
        )
        try:
            cap_by_bank = quantize_bet(self.cover50_cap_ratio * current_balance)
            if bet > cap_by_bank: bet = cap_by_bank
        except Exception: pass
        if bet < self.min_bet: bet = self.min_bet
        return bet

    def _maybe_auto_reset_profit(self, current_balance: Decimal):
        if not self.auto_reset_profit_enabled:
            return
        if self.auto_reset_profit_triggered:
            return
        if self.profit_global >= self.auto_reset_profit_threshold:
            self.reset_cover_base(current_balance)
            self.auto_reset_profit_triggered = True
            self._log(f"[{self.bot_id}] ✅ Auto reset cover base by profit threshold {self.auto_reset_profit_threshold:.8f} reached (profit_global={self.profit_global:.8f}).")

    def start(self):
        if not self.config.api_key:
            self._log(f"[{self.bot_id}] Нет API ключа.")
            return
        if self.strategy is None:
            self._log(f"[{self.bot_id}] Нет стратегии.")
            return

        self.is_running = True
        self.paused = False
        current_balance = self.get_current_balance()
        self.reset_stats()
        if self.cover_base_bank is None:
            self.cover_base_bank = current_balance
        self._log(f"[{self.bot_id}] Старт баланса: {current_balance:.8f}; cover_base_bank={self.cover_base_bank:.8f}")
        if self.initial_bank is None: self.initial_bank = current_balance
        if self.last_successful_bank is None: self.last_successful_bank = self.initial_bank

        while self.is_running:
            while self.paused and self.is_running:
                time.sleep(0.1)

            self.fetch_settings_if_needed()
            current_balance = self.get_current_balance()

            if self.cover50_auto_remaining > 0 and self.auto_cover_payout is not None:
                payout = self.auto_cover_payout
            else:
                try:
                    payout, _, _, _ = self.strategy.next_payout_and_bet({"min_bet": self.min_bet})
                except Exception as e:
                    self._log(f"[{self.bot_id}] Ошибка стратегии: {e}")
                    time.sleep(1)
                    continue

            if self.strategy and hasattr(self.strategy, "max_payout"):
                try:
                    if self._prev_payout is not None and Decimal(self._prev_payout) == self.strategy.max_payout and payout == self.strategy.start_payout:
                        self.payout_wraps += 1
                        self._log(f"[{self.bot_id}] [WRAP] max→reset (#{self.payout_wraps})")
                except Exception: pass
            self._prev_payout = payout

            try: chance_decimal = (Decimal("100") / payout)
            except Exception: chance_decimal = Decimal("99.99")
            if chance_decimal < MIN_API_CHANCE: chance_decimal = MIN_API_CHANCE
            if chance_decimal > MAX_API_CHANCE: chance_decimal = MAX_API_CHANCE

            bet = Decimal("0.001")
            manual_cover = False
            auto_cover = False

            if self.cover50_pending:
                b_man = self._cover50_bet(payout, current_balance)
                if b_man is not None:
                    bet = b_man
                    manual_cover = True
                self.cover50_pending = False
            elif self.cover50_auto_remaining > 0 and self.auto_cover_payout is not None:
                b_auto = self._cover50_bet(payout, current_balance)
                if b_auto is not None:
                    bet = b_auto
                    auto_cover = True
                self.cover50_auto_remaining -= 1
                if self.cover50_auto_remaining == 0:
                    self.auto_cover_payout = None

            bet = quantize_bet(bet)

            if bet > current_balance:
                self._log(f"[{self.bot_id}] ❌ Недостаточно баланса. Баланс={current_balance:.8f} Ставка={bet:.8f}")
                break

            client_seed = self.client_seed or self.api.generate_client_seed()
            res = self.api.placebet(self.config.coin, self.config.api_key,
                                    float(bet), float(payout), True, client_seed)

            if isinstance(res, dict) and res.get("error"):
                self._log(f"[{self.bot_id}] API ошибка: {res.get('error')}")
                time.sleep(1); continue

            profit = safe_decimal(res.get("Profit", "0"))
            new_balance = safe_decimal(res.get("Balance", current_balance))
            roll_val = res.get("Roll", None)
            roll_str = f"{roll_val:.10f}" if isinstance(roll_val, float) else ("n/a" if roll_val is None else str(roll_val))
            win = profit > 0

            if win:
                if manual_cover or auto_cover:
                    self.cover50_profit_total += profit
                    if manual_cover:
                        self.cover50_profit_manual += profit
                        self.cover50_wins_manual += 1
                    if auto_cover:
                        self.cover50_profit_auto += profit
                        self.cover50_wins_auto += 1
                    self.cover50_wins_total += 1
                self.stats["wins"] += 1
                self.stats["profit"] += profit
                self.stats["current_streak"] = max(0, self.stats["current_streak"] + 1)
                self.loss_sum = Decimal("0")
                self.streak = 0
                if self.last_successful_bank is None or new_balance > self.last_successful_bank:
                    self.last_successful_bank = new_balance

                if self.auto_trigger_min <= payout <= self.auto_trigger_max:
                    self.cover50_auto_remaining = 2
                    self.auto_cover_payout = payout
                    self._log(f"[{self.bot_id}] ▶ Авто Cover50 старт: payout={int(payout)}, 2 спина подряд.")

                if self.stop_on_win:
                    self.paused = True

                prefix = "[WIN-COVER50]" if (manual_cover or auto_cover) else "[WIN]"
                self._log(f"{prefix} spin {self.spin_count + 1} payout={int(payout)} roll={roll_str} bet={bet:.8f} profit={profit:.8f}")
            else:
                if manual_cover or auto_cover:
                    self.cover50_losses_total += 1
                self.stats["losses"] += 1
                self.stats["current_streak"] = min(0, self.stats["current_streak"] - 1)
                self.loss_sum += bet
                self.streak += 1
                if self.loss_sum > self.stats["max_loss_sum"]:
                    self.stats["max_loss_sum"] = self.loss_sum
                if bet > self.stats["max_bet"]:
                    self.stats["max_bet"] = bet
                prefix = "[LOSS-COVER50]" if (manual_cover or auto_cover) else "[LOSS]"
                self._log(f"{prefix} spin {self.spin_count + 1} payout={int(payout)} roll={roll_str} bet={bet:.8f}")

            self.stats["total_bets"] += 1
            self.stats["total_wagered"] += bet
            self.profit_global = new_balance - (self.initial_bank if self.initial_bank is not None else Decimal("0"))

            # Авто-сброс базы по прибыли
            self._maybe_auto_reset_profit(new_balance)

            self._stats()
            self._bank(new_balance)

            if self.manager_ref:
                try: self.manager_ref.check_global_take_profit()
                except: pass

            self.spin_count += 1
            self.local_nonce += 1
            time.sleep(max(0.01, self.config.speed_ms / 1000.0))

        self._log(f"[{self.bot_id}] 🛑 Остановлен")

    def stop(self):
        self.is_running = False
        self.paused = False

class BotTab:
    def __init__(self, parent_notebook, manager, bot_index:int, initial_config:BetConfig=None):
        self.manager = manager
        self.bot_index = bot_index
        self.bot_name = f"Bot-{bot_index}"
        self.frame = ttk.Frame(parent_notebook)
        parent_notebook.add(self.frame, text=self.bot_name)

        left = ttk.Frame(self.frame); left.pack(side="left", fill="y", padx=6, pady=6)
        right = ttk.Frame(self.frame); right.pack(side="right", fill="both", expand=True, padx=6, pady=6)

        self.api_entry = ttk.Entry(left, width=32, show="*")
        self.coin_box = ttk.Combobox(left, values=["BTC","USDT","XLM","ETH","DOGE","LTC"], width=8, state="readonly")
        self.bet_entry = ttk.Entry(left, width=12)
        self.enforced_min_entry = ttk.Entry(left, width=12)
        self.maxbet_entry = ttk.Entry(left, width=12)
        self.speed_box = ttk.Spinbox(left, from_=10, to=5000, increment=10, width=8)
        self.minbet_refresh_spin = ttk.Spinbox(left, from_=5, to=600, increment=5, width=8)
        self.target_min_bets_spin = ttk.Spinbox(left, from_=1, to=1000, increment=1, width=6)
        self.min_payout_entry = ttk.Entry(left, width=12)
        self.max_payout_entry = ttk.Entry(left, width=12)

        self.pause_on_fail_var = tk.BooleanVar(value=False)
        self.stop_on_win_var = tk.BooleanVar(value=False)
        self.seed_entry = ttk.Entry(left, width=20)

        self.start_btn = ttk.Button(left, text="Start", command=self.start_bot)
        self.pause_btn = ttk.Button(left, text="Pause", command=self.toggle_pause, state="disabled")
        self.stop_btn = ttk.Button(left, text="Stop", command=self.stop_bot, state="disabled")
        self.seed_btn = ttk.Button(left, text="Gen Seed", command=self.generate_seed)

        cover_frame = ttk.LabelFrame(left, text="Cover 50% Drawdown", padding=6)
        self.cover50_cap_entry = ttk.Entry(cover_frame, width=8)
        self.cover50_btn = ttk.Button(cover_frame, text="Cover 50%", command=self.cover50_action)
        self.cover_base_btn = ttk.Button(cover_frame, text="Reset Cover Base", command=self.cover_base_reset_action)

        # Новые элементы авто-сброса по прибыли
        self.auto_reset_profit_enabled_var = tk.BooleanVar(value=False)
        self.auto_reset_profit_chk = ttk.Checkbutton(cover_frame, text="Auto reset by profit",
                                                     variable=self.auto_reset_profit_enabled_var)
        self.auto_reset_profit_entry = ttk.Entry(cover_frame, width=8)

        ttk.Label(left, text="API Key:").grid(row=0,column=0,sticky="w"); self.api_entry.grid(row=0,column=1,padx=4)
        ttk.Label(left, text="Coin:").grid(row=1,column=0,sticky="w"); self.coin_box.grid(row=1,column=1,padx=4)
        ttk.Label(left, text="Base bet:").grid(row=2,column=0,sticky="w"); self.bet_entry.grid(row=2,column=1,padx=4)
        ttk.Label(left, text="Enforced min:").grid(row=3,column=0,sticky="w"); self.enforced_min_entry.grid(row=3,column=1,padx=4)
        ttk.Label(left, text="Max bet limit:").grid(row=4,column=0,sticky="w"); self.maxbet_entry.grid(row=4,column=1,padx=4)
        ttk.Label(left, text="Speed ms:").grid(row=5,column=0,sticky="w"); self.speed_box.grid(row=5,column=1,padx=4)
        ttk.Label(left, text="Min settings refresh s:").grid(row=6,column=0,sticky="w"); self.minbet_refresh_spin.grid(row=6,column=1,padx=4)
        ttk.Label(left, text="Target M:").grid(row=7,column=0,sticky="w"); self.target_min_bets_spin.grid(row=7,column=1,padx=4)
        ttk.Label(left, text="Min payout:").grid(row=8,column=0,sticky="w"); self.min_payout_entry.grid(row=8,column=1,padx=4)
        ttk.Label(left, text="Max payout:").grid(row=9,column=0,sticky="w"); self.max_payout_entry.grid(row=9,column=1,padx=4)
        ttk.Checkbutton(left, text="Pause on FAIL", variable=self.pause_on_fail_var,
                        command=self._on_pause_on_fail_toggled).grid(row=10,column=0,columnspan=2,sticky="w")
        ttk.Checkbutton(left, text="Stop on WIN", variable=self.stop_on_win_var,
                        command=self._on_stop_on_win_toggled).grid(row=11,column=0,columnspan=2,sticky="w")
        ttk.Label(left, text="Client Seed:").grid(row=12,column=0,sticky="w"); self.seed_entry.grid(row=12,column=1,padx=4)

        btnf = ttk.Frame(left); btnf.grid(row=13,column=0,columnspan=2,pady=(8,0))
        self.start_btn.pack(in_=btnf, side="left", padx=4)
        self.pause_btn.pack(in_=btnf, side="left", padx=4)
        self.stop_btn.pack(in_=btnf, side="left", padx=4)
        self.seed_btn.pack(in_=btnf, side="left", padx=4)

        cover_frame.grid(row=14, column=0, columnspan=2, sticky="w", pady=(8,0))
        ttk.Label(cover_frame, text="Cap % of bank:").grid(row=0, column=0, sticky="w")
        self.cover50_cap_entry.grid(row=0, column=1, padx=4); self.cover50_cap_entry.insert(0, "2.0")
        self.cover50_btn.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(4,0))
        self.cover_base_btn.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(4,0))

        ttk.Label(cover_frame, text="Profit >=").grid(row=3, column=0, sticky="w")
        self.auto_reset_profit_entry.grid(row=3, column=1, padx=4)
        self.auto_reset_profit_entry.insert(0, "1.0")
        self.auto_reset_profit_chk.grid(row=4, column=0, columnspan=2, sticky="w", pady=(4,0))

        bank_frame = ttk.LabelFrame(right, text="Bank", padding=6)
        bank_frame.pack(fill="x", pady=(0,6))
        self.initial_bank_lbl = ttk.Label(bank_frame, text="Initial: 0.00000000 USDT"); self.initial_bank_lbl.pack(anchor="w")
        self.last_bank_lbl = ttk.Label(bank_frame, text="Last successful: 0.00000000 USDT"); self.last_bank_lbl.pack(anchor="w")
        self.current_bank_lbl = ttk.Label(bank_frame, text="Current: 0.00000000 USDT"); self.current_bank_lbl.pack(anchor="w")
        self.cover_base_lbl = ttk.Label(bank_frame, text="Cover Base: 0.00000000 USDT"); self.cover_base_lbl.pack(anchor="w")
        self.cover50_profit_lbl = ttk.Label(bank_frame, text="Cover 50% profit: 0.00000000 (M:0.00000000, A:0.00000000) USDT"); self.cover50_profit_lbl.pack(anchor="w")
        self.cover50_wins_lbl = ttk.Label(bank_frame, text="Cover 50% wins: Total=0 (M:0, A:0) losses=0"); self.cover50_wins_lbl.pack(anchor="w")

        ttk.Label(right, text=f"{self.bot_name} Last 20 bets").pack(anchor="w")
        self.log_text = scrolledtext.ScrolledText(right, height=18)
        self.log_text.pack(fill="both", expand=True)
        self.log_text.tag_config("win", foreground="green")
        self.log_text.tag_config("loss", foreground="red")

        self._bet_lines = deque(maxlen=20)
        os.makedirs("logs", exist_ok=True)
        safe_name = self.bot_name.replace("/", "_").replace("\\", "_")
        self.log_file_path = os.path.join("logs", f"{safe_name}.txt")

        if initial_config:
            self.coin_box.set(initial_config.coin)
            self.bet_entry.insert(0, str(initial_config.base_bet))
            self.enforced_min_entry.insert(0, str(initial_config.min_bet_enforced))
            self.maxbet_entry.insert(0, str(initial_config.max_bet_limit))
            self.speed_box.set(initial_config.speed_ms)
            self.minbet_refresh_spin.set(initial_config.min_bet_refresh_secs)
            self.target_min_bets_spin.set(initial_config.target_min_bets_on_win)
        else:
            self.coin_box.set("USDT")
            self.bet_entry.insert(0, "0.001")
            self.enforced_min_entry.insert(0, "0.001")
            self.maxbet_entry.insert(0, "1.0")
            self.speed_box.set(50)
            self.minbet_refresh_spin.set(30)
            self.target_min_bets_spin.set(10)

        self.min_payout_entry.insert(0, "100")
        self.max_payout_entry.insert(0, "9999")

        self.bot = None
        self.bot_thread = None

    def _file_log(self, msg: str):
        try:
            ts = time.strftime("%Y-%m-%d %H:%M:%S")
            with open(self.log_file_path, "a", encoding="utf-8") as f: f.write(f"{ts} {msg}\n")
        except Exception as e: print(f"[{self.bot_name}] File log error: {e}")

    def _render_bet_log(self):
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        for stored in self._bet_lines:
            line, tag = stored
            self.log_text.insert("end", line + "\n", (tag if tag else ()))
        self.log_text.see("end")
        self.log_text.configure(state="normal")

    def log_bet(self, raw_line: str):
        line_lower = raw_line.lower()
        tag = None
        if line_lower.startswith("[win"):
            tag = "win"
        elif line_lower.startswith("[loss"):
            tag = "loss"
        self._bet_lines.append((raw_line, tag))
        self._render_bet_log()

    def log(self, msg):
        ts = time.strftime("%H:%M:%S")
        print(f"{ts} [{self.bot_name}] {msg}")
        self._file_log(f"[{self.bot_name}] {msg}")
        if msg.startswith("[WIN") or msg.startswith("[LOSS"):
            self.log_bet(msg)

    def _parse_decimal(self, value, default):
        try:
            if value is None: return Decimal(default)
            s = str(value).strip()
            if s == "": return Decimal(default)
            return Decimal(s)
        except (InvalidOperation, ValueError):
            return Decimal(default)

    def _parse_int(self, value, default):
        try:
            if value is None: return int(default)
            s = str(value).strip()
            if s == "": return int(default)
            return int(float(s))
        except Exception:
            return int(default)

    def apply_settings_to_config(self):
        cfg = BetConfig()
        cfg.coin = self.coin_box.get().strip() or cfg.coin
        cfg.api_key = self.api_entry.get().strip() or ""
        cfg.base_bet = self._parse_decimal(self.bet_entry.get(), cfg.base_bet)
        cfg.min_bet_enforced = self._parse_decimal(self.enforced_min_entry.get(), cfg.min_bet_enforced)
        cfg.max_bet_limit = self._parse_decimal(self.maxbet_entry.get(), cfg.max_bet_limit)
        cfg.speed_ms = self._parse_int(self.speed_box.get(), cfg.speed_ms)
        cfg.min_bet_refresh_secs = self._parse_int(self.minbet_refresh_spin.get(), cfg.min_bet_refresh_secs)
        cfg.target_min_bets_on_win = self._parse_int(self.target_min_bets_spin.get(), cfg.target_min_bets_on_win)
        return cfg

    def start_bot(self):
        try:
            cfg = self.apply_settings_to_config()
        except Exception as e:
            self.manager.enqueue(('log', self.bot_name, f"Ошибка настроек: {e}"))
            self.manager.enqueue(('trace', self.bot_name, traceback.format_exc()))
            return
        if not cfg.api_key:
            messagebox.showerror("Error", "Требуется API Key")
            return

        try: min_payout = Decimal(str(self.min_payout_entry.get()).strip())
        except Exception: min_payout = Decimal("100")
        try: max_payout = Decimal(str(self.max_payout_entry.get()).strip())
        except Exception: max_payout = Decimal("9999")
        if min_payout < 2 or max_payout <= min_payout:
            messagebox.showerror("Error", "Неверный диапазон payout")
            return
        if max_payout > Decimal("20000"):
            messagebox.showerror("Error", "Max payout > 20000")
            return

        pause_on_fail = bool(self.pause_on_fail_var.get())
        stop_on_win = bool(self.stop_on_win_var.get())

        api_client = APIClient()
        bot_id = f"{self.bot_name}"

        def log_cb(msg: str): self.manager.enqueue(('log', bot_id, msg))
        bank_cb = lambda stats: self.manager.enqueue(('bank', bot_id, stats))
        stats_cb = lambda stats: self.manager.enqueue(('stats', bot_id, stats))

        try:
            self.bot = CryptoGamesBot(
                bot_id, api_client, cfg,
                log_cb, bank_cb, stats_cb,
                pause_on_fail=pause_on_fail,
                stop_on_win=stop_on_win,
                executor=self.manager.executor
            )

            def linear_factory():
                return LinearPayoutStrategy(start_payout=min_payout, max_payout=max_payout)

            self.bot.set_strategy_factories([linear_factory])
            self.bot.set_strategy(linear_factory())

            seed = self.seed_entry.get().strip()
            if seed:
                self.bot.client_seed = seed

            # Настройки авто-сброса по прибыли
            try:
                thr = Decimal(str(self.auto_reset_profit_entry.get()).strip())
                if thr <= 0: thr = Decimal("1.0")
            except Exception:
                thr = Decimal("1.0")
            self.bot.auto_reset_profit_threshold = thr
            self.bot.auto_reset_profit_enabled = bool(self.auto_reset_profit_enabled_var.get())

            self.bot.manager_ref = self.manager

            self.start_btn.config(state="disabled"); self.pause_btn.config(state="normal"); self.stop_btn.config(state="normal")
            self.bot_thread = threading.Thread(target=self.bot.start, daemon=True)
            self.bot_thread.start()
            self.manager.register_bot(self.bot, self)
            self.manager.enqueue(('log', bot_id,
                                  f"Запущен (payout {int(min_payout)}..{int(max_payout)} "
                                  f"| auto_reset_profit_enabled={self.bot.auto_reset_profit_enabled} "
                                  f"threshold={self.bot.auto_reset_profit_threshold})"))
        except Exception as e:
            self.manager.enqueue(('log', bot_id, f"Ошибка запуска: {e}"))
            self.manager.enqueue(('trace', bot_id, traceback.format_exc()))

    def cover50_action(self):
        if not self.bot or not self.bot.is_running:
            self.log("Бот не запущен для Cover 50%.")
            return
        try: cap_pct = Decimal(str(self.cover50_cap_entry.get()).strip())
        except Exception: cap_pct = Decimal("2.0")
        if cap_pct < Decimal("0.1"): cap_pct = Decimal("0.1")
        if cap_pct > Decimal("50"): cap_pct = Decimal("50")
        self.bot.request_cover50(cap_pct / Decimal("100"))
        self.log(f"Cover 50% вручную (cap {cap_pct:.2f}%).")

    def cover_base_reset_action(self):
        if not self.bot or not self.bot.is_running:
            self.log("Бот не запущен для Reset Cover Base.")
            return
        current_balance = self.bot.get_current_balance()
        self.bot.reset_cover_base(current_balance)
        self.log(f"Cover base обновлена: {current_balance:.8f}")

    def toggle_pause(self):
        if not self.bot: return
        paused = self.bot.pause_toggle()
        self.pause_btn.config(text="Resume" if paused else "Pause")
        self.manager.enqueue(('log', self.bot_name, "Paused" if paused else "Resumed"))

    def stop_bot(self):
        if self.bot:
            try: self.bot.stop()
            except Exception as e:
                self.manager.enqueue(('log', self.bot_name, f"Ошибка остановки: {e}"))
            self.manager.unregister_bot(self.bot.bot_id)
        self.start_btn.config(state="normal"); self.pause_btn.config(state="disabled", text="Pause"); self.stop_btn.config(state="disabled")
        self.manager.enqueue(('log', self.bot_name, "Stopped"))

    def generate_seed(self):
        seed = APIClient().generate_client_seed()
        self.seed_entry.delete(0, tk.END)
        self.seed_entry.insert(0, seed)
        self.manager.enqueue(('log', self.bot_name, f"Client seed: {seed}"))

    def _on_pause_on_fail_toggled(self):
        val = bool(self.pause_on_fail_var.get())
        if self.bot:
            self.bot.pause_on_fail = val
            self.manager.enqueue(('log', self.bot_name, f"Pause on FAIL = {val}"))

    def _on_stop_on_win_toggled(self):
        val = bool(self.stop_on_win_var.get())
        if self.bot:
            self.bot.stop_on_win = val
            self.manager.enqueue(('log', self.bot_name, f"Stop on WIN = {val}"))

    def update_bank_ui(self, stats: dict):
        try:
            coin = self.bot.config.coin if self.bot else "USDT"
            initial = safe_decimal(stats.get("initial_bank"))
            last = safe_decimal(stats.get("last_successful_bank", initial))
            current = safe_decimal(stats.get("current_bank"))
            cov_base = safe_decimal(stats.get("cover_base_bank", current))
            cov_total = safe_decimal(stats.get("cover50_profit_total"))
            cov_man = safe_decimal(stats.get("cover50_profit_manual"))
            cov_auto = safe_decimal(stats.get("cover50_profit_auto"))
            cov_w_total = int(stats.get("cover50_wins_total", 0))
            cov_w_man = int(stats.get("cover50_wins_manual", 0))
            cov_w_auto = int(stats.get("cover50_wins_auto", 0))
            cov_l_total = int(stats.get("cover50_losses_total", 0))
        except Exception:
            initial=last=current=cov_base=Decimal("0"); coin="USDT"
            cov_total=cov_man=cov_auto=Decimal("0")
            cov_w_total=cov_w_man=cov_w_auto=cov_l_total=0

        def _upd():
            self.initial_bank_lbl.config(text=f"Initial: {initial:.8f} {coin}")
            self.last_bank_lbl.config(text=f"Last successful: {last:.8f} {coin}")
            self.current_bank_lbl.config(text=f"Current: {current:.8f} {coin}")
            self.cover_base_lbl.config(text=f"Cover Base: {cov_base:.8f} {coin}")
            col = "darkgreen" if current >= initial else "red"
            self.current_bank_lbl.config(foreground=col)
            self.cover50_profit_lbl.config(
                text=f"Cover 50% profit: {cov_total:.8f} (M:{cov_man:.8f}, A:{cov_auto:.8f}) {coin}"
            )
            self.cover50_wins_lbl.config(
                text=f"Cover 50% wins: Total={cov_w_total} (M:{cov_w_man}, A:{cov_w_auto}) losses={cov_l_total}"
            )
        try: self.frame.after(0, _upd)
        except: _upd()

class BotManagerApp:
    def __init__(self, ui_poll_ms: int = 100):
        self.root = tk.Tk()
        self.root.title("Crypto.Games Multi-Bot Manager")
        self.root.geometry("1260x880")
        self.bot_tabs = {}
        self.active_bots = {}
        self.all_banks = {}
        self.lock = threading.Lock()
        self.ui_queue = queue.Queue()
        max_workers = min(32, (os.cpu_count() or 4) * 5)
        self.executor = ThreadPoolExecutor(max_workers=max_workers)
        self.global_take_profit_enabled = tk.BooleanVar(value=False)
        self.global_take_profit_percent_var = tk.StringVar(value="10")
        self.global_tp_active = False
        self.tp_new_initials = {}
        self.ui_poll_ms = ui_poll_ms
        self._build_ui()
        self.new_bot_tab()
        self.root.after(self.ui_poll_ms, self._process_ui_queue)

    def _build_ui(self):
        top = ttk.Frame(self.root); top.pack(fill="x", padx=6, pady=6)
        self.agg_label = ttk.Label(top, text="Aggregate: Current=0.00000000 Profit=+0.00000000")
        self.agg_label.pack(side="left", padx=(4,20))
        ttk.Button(top, text="New Bot", command=self.new_bot_tab).pack(side="left")
        ttk.Button(top, text="Start All", command=self.start_all_bots).pack(side="left", padx=6)
        ttk.Button(top, text="Stop All", command=self.stop_all_bots).pack(side="left", padx=6)
        ttk.Label(top, text="Global TP %:").pack(side="left", padx=(16,4))
        ttk.Entry(top, textvariable=self.global_take_profit_percent_var, width=6).pack(side="left", padx=2)
        ttk.Checkbutton(top, text="Enable Global TP %", variable=self.global_take_profit_enabled,
                        command=self._on_global_tp_toggle).pack(side="left", padx=6)
        self.bot_notebook = ttk.Notebook(self.root); self.bot_notebook.pack(fill="both", expand=True, padx=6, pady=(0,6))

    def _on_global_tp_toggle(self):
        self.check_global_take_profit(force=True)

    def new_bot_tab(self):
        idx = len(self.bot_tabs) + 1
        tab = BotTab(self.bot_notebook, self, idx)
        self.bot_tabs[tab.bot_name] = tab
        self.bot_notebook.select(tab.frame)

    def register_bot(self, bot: CryptoGamesBot, bottab: BotTab):
        with self.lock:
            init = safe_decimal(getattr(bot, "initial_bank", "0"))
            curr = init
            prof = safe_decimal(getattr(bot, "profit_global", "0"))
            self.active_bots[bot.bot_id] = bot
            self.bot_tabs[bot.bot_id] = bottab
            self.all_banks[bot.bot_id] = {"current_bank": curr, "profit_global": prof, "initial_bank": init}
        self._update_aggregate_label()

    def unregister_bot(self, bot_id: str):
        with self.lock:
            self.active_bots.pop(bot_id, None)
            self.all_banks.pop(bot_id, None)
        self._update_aggregate_label()

    def enqueue(self, t):
        try: self.ui_queue.put_nowait(t)
        except queue.Full: pass

    def _process_ui_queue(self):
        processed = 0
        while processed < 500:
            try:
                typ, bot_id, payload = self.ui_queue.get_nowait()
            except queue.Empty:
                break
            if typ == 'log':
                tab = self.bot_tabs.get(bot_id)
                if tab:
                    tab._file_log(payload if isinstance(payload,str) else str(payload))
                    if isinstance(payload,str) and (payload.startswith("[WIN") or payload.startswith("[LOSS")):
                        tab.log_bet(payload)
                print(f"[{bot_id}] {payload}")
            elif typ == 'trace':
                print(payload)
            elif typ == 'bank':
                stats = payload
                curr = safe_decimal(stats.get("current_bank"))
                init = safe_decimal(stats.get("initial_bank"))
                prof = safe_decimal(stats.get("profit_global"))
                if init <= 0: init = curr
                with self.lock:
                    self.all_banks[bot_id] = {"current_bank": curr, "profit_global": prof, "initial_bank": init}
                tab = self.bot_tabs.get(bot_id)
                if tab: tab.update_bank_ui(stats)
                self._update_aggregate_label()
            processed += 1
        self.check_global_take_profit()
        self.root.after(self.ui_poll_ms, self._process_ui_queue)

    def _update_aggregate_label(self):
        with self.lock:
            total_current = sum(safe_decimal(v.get("current_bank")) for v in self.all_banks.values()) if self.all_banks else Decimal("0")
            total_profit = sum(safe_decimal(v.get("profit_global")) for v in self.all_banks.values()) if self.all_banks else Decimal("0")
        sign = "+" if total_profit >= 0 else ""
        col = "darkgreen" if total_profit >= 0 else "red"
        try:
            self.agg_label.config(text=f"Aggregate: Current={total_current:.8f} Profit={sign}{total_profit:.8f}", foreground=col)
        except: pass

    def _aggregate_initial_and_current(self):
        with self.lock:
            total_current = Decimal("0"); total_initial = Decimal("0")
            for v in self.all_banks.values():
                curr = safe_decimal(v.get("current_bank"))
                init = safe_decimal(v.get("initial_bank"))
                if init <= 0: init = curr
                total_current += curr
                total_initial += init
        return total_initial, total_current

    def _parse_tp_percent(self):
        try:
            p = Decimal(str(self.global_take_profit_percent_var.get()).strip())
            if p <= 0: return None
            return p
        except: return None

    def check_global_take_profit(self, force=False):
        if not self.global_take_profit_enabled.get(): return
        tp = self._parse_tp_percent()
        if tp is None: return
        total_initial, total_current = self._aggregate_initial_and_current()
        if total_initial <= 0: return
        target = total_initial * (Decimal("1") + tp/Decimal("100"))
        if total_current >= target:
            if not self.global_tp_active or force:
                self._trigger_global_tp(total_current, total_initial, tp)

    def _trigger_global_tp(self, total_current: Decimal, total_initial: Decimal, tp: Decimal):
        self.global_tp_active = True
        growth = (total_current - total_initial)*Decimal("100")/total_initial
        print(f"[Manager] TP: рост={growth:.2f}% >= {tp:.2f}% пауза 5с + rebase")
        with self.lock:
            self.tp_new_initials = {bid: safe_decimal(rec.get("current_bank")) for bid, rec in self.all_banks.items()}
            for bot in self.active_bots.values():
                bot.paused = True
                bot._log(f"[{bot.bot_id}] TP pause 5s")
        self.root.after(5000, self._resume_after_tp)

    def _resume_after_tp(self):
        with self.lock:
            for bot_id, bot in self.active_bots.items():
                new_initial = self.tp_new_initials.get(bot_id, Decimal("0"))
                if new_initial <= 0:
                    new_initial = safe_decimal(self.all_banks.get(bot_id, {}).get("current_bank"))
                rec = self.all_banks.get(bot_id, {}) or {}
                rec["initial_bank"] = new_initial
                rec["current_bank"] = new_initial
                self.all_banks[bot_id] = rec
                bot.restart_after_tp(new_initial)
                bot.paused = False
            self.global_tp_active = False
            self.tp_new_initials = {}
        print("[Manager] TP resume done")

    def stop_all_bots(self):
        with self.lock:
            bots = list(self.active_bots.values())
        for b in bots:
            try: b.stop()
            except: pass
        print("All bots stop requested")

    def start_all_bots(self):
        for tab in list(self.bot_tabs.values()):
            try:
                if not tab.bot or not tab.bot.is_running:
                    tab.start_bot()
            except Exception as e:
                tb = traceback.format_exc()
                self.enqueue(('log', tab.bot_name, f"Error starting: {e}"))
                self.enqueue(('trace', tab.bot_name, tb))
        self.enqueue(('log', 'Manager', "Start all requested"))

    def run(self):
        self.root.mainloop()

if __name__ == "__main__":
    app = BotManagerApp(ui_poll_ms=100)
    app.run()