#!/usr/bin/env python3
# Crypto.Games multi-bot GUI — multithreaded UI queue
# Изменение по просьбе пользователя: основная стратегия ставит ставку так, чтобы покрыть весь убыток за серию (loss_total).
# Больше ничего не менялось.

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
MAX_PAYOUT_DEFAULT = Decimal("9999")

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
            try:
                return {"error": r.json()}
            except Exception:
                return {"error": str(e)}

    def _post(self, path: str, payload: dict):
        url = f"{self.base}{path}"
        try:
            r = self.session.post(url, json=payload, timeout=self.timeout)
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            try:
                return {"error": r.json()}
            except Exception:
                return {"error": str(e)}

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
    try:
        return bet.quantize(q, rounding=ROUND_DOWN)
    except Exception:
        return bet

def safe_decimal(val, default="0"):
    if val is None:
        return Decimal(default)
    try:
        return Decimal(str(val))
    except Exception:
        return Decimal(default)

def compute_bet_for_target_profit(
    payout: Decimal,
    target_profit: Decimal,
    min_bet: Decimal,
    max_bet_limit: Decimal | None,
    current_bank: Decimal,
    house_edge_frac: Decimal | None = None
) -> Decimal:
    try:
        p = Decimal(payout)
    except Exception:
        p = Decimal("2")
    denom = p - Decimal("1")
    try:
        ef = Decimal(house_edge_frac or 0)
        if ef > 0 and ef < 1:
            denom = denom * (Decimal("1") - ef)
    except Exception:
        pass
    if denom <= 0:
        denom = Decimal("1")
    desired = Decimal(target_profit) / denom
    bet = quantize_bet(desired)
    if max_bet_limit is not None:
        try:
            mb = Decimal(str(max_bet_limit))
            if bet > mb:
                bet = mb
        except Exception:
            pass
    if current_bank is not None:
        try:
            cb = Decimal(str(current_bank))
            if bet > cb:
                bet = cb
        except Exception:
            pass
    if bet < min_bet:
        bet = min_bet
    if bet <= Decimal("0"):
        bet = Decimal("0.00000001")
    return quantize_bet(bet)

class LinearPayoutStrategy:
    def __init__(self, start_payout=Decimal("1000"), max_payout=MAX_PAYOUT_DEFAULT):
        self.start_payout = Decimal(start_payout)
        self.max_payout = Decimal(max_payout)
        self.current_payout = Decimal(start_payout)

    def reset(self):
        self.current_payout = Decimal(self.start_payout)

    def next_payout(self):
        payout = self.current_payout
        nxt = payout + Decimal(1)
        if nxt > self.max_payout:
            nxt = Decimal(self.start_payout)
        self.current_payout = nxt
        return payout

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

        self.house_edge_frac = Decimal("0")

        self.balance_at_cycle_start = None
        self.cycle_loss = Decimal("0")
        self.last_spin_was_loss = False

        # Режимы восстановления (как были):
        self.recover66_active = False
        self.recover66_wins_target = 3
        self.recover66_wins_done = 0
        self.bank_fixed_at_trigger = None
        self.recover66_last_info = ""

        self.periodic_trigger_interval = 200
        self.periodic_recovery_active = False
        self.periodic_recovery_spins_done = 0
        self.periodic_recovery_max_spins = 100
        self.periodic_payout_min = Decimal("100")
        self.periodic_payout_max = Decimal("200")
        self.periodic_payout_current = Decimal("100")
        self.recovery_spent = Decimal("0")
        self.loss_total = Decimal("0")

    def pause_toggle(self):
        self.paused = not self.paused
        return self.paused

    def set_strategy(self, strategy_obj):
        self.strategy = strategy_obj
        try:
            self.strategy.reset()
        except Exception:
            pass

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
            try:
                self.strategy.reset()
            except:
                pass
        self._log(f"[{self.bot_id}] ▶ TP restart initial={self.initial_bank:.8f}")

    def _log(self, msg):
        ts = time.strftime("%H:%M:%S")
        try:
            print(f"{ts} [{self.bot_id}] {msg}")
        except Exception:
            pass
        try:
            self.log_cb(msg)
        except Exception:
            pass

    def _push_bank_payload(self, bal: Decimal):
        if self.initial_bank is None:
            self.initial_bank = bal
        data = {
            "initial_bank": self.initial_bank,
            "last_successful_bank": self.last_successful_bank if self.last_successful_bank is not None else self.initial_bank,
            "current_bank": bal,
            "profit_global": self.profit_global,
            "balance_at_cycle_start": self.balance_at_cycle_start if self.balance_at_cycle_start is not None else bal,
            "cycle_loss": self.cycle_loss,
            "recover66_active": self.recover66_active,
            "recover66_wins_done": self.recover66_wins_done,
            "recover66_info": self.recover66_last_info,
            "periodic_active": self.periodic_recovery_active,
            "periodic_spins": self.periodic_recovery_spins_done,
            "recovery_spent": self.recovery_spent,
            "loss_total": self.loss_total,
            "bot_id": self.bot_id
        }
        try:
            self.bank_cb(data)
        except:
            pass

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
        try:
            self.stats_cb(s)
        except:
            pass

    def get_current_balance(self):
        if not self.config.api_key:
            return Decimal("0")
        try:
            res = self.api.balance(self.config.coin, self.config.api_key)
            if isinstance(res, dict) and res.get("Balance") is not None:
                bal = safe_decimal(res.get("Balance"))
                self._push_bank_payload(bal)
                return bal
        except Exception:
            pass
        try:
            usr = self.api.user(self.config.coin, self.config.api_key)
            if isinstance(usr, dict) and usr.get("Balance") is not None:
                bal = safe_decimal(usr.get("Balance"))
                self._push_bank_payload(bal)
                return bal
        except Exception:
            pass
        return Decimal("0")

    def fetch_settings_if_needed(self):
        now = time.time()
        if now - self._last_min_bet_fetch < self.config.min_bet_refresh_secs:
            return
        self._last_min_bet_fetch = now
        res = self.api.settings(self.config.coin)
        if isinstance(res, dict) and res.get("MinBet") is not None:
            try:
                self.min_bet = safe_decimal(res.get("MinBet"))
                edge_raw = res.get("Edge")
                try:
                    edge_pct = Decimal(str(edge_raw))
                    if edge_pct > 0:
                        self.house_edge_frac = edge_pct / Decimal("100")
                    else:
                        self.house_edge_frac = Decimal("0")
                except Exception:
                    self.house_edge_frac = Decimal("0")
                self._log(f"[{self.bot_id}] 🔎 Settings: MinBet={self.min_bet} Edge={edge_raw} (frac={self.house_edge_frac})")
            except Exception as e:
                self._log(f"[{self.bot_id}] ⚠️ Failed parsing settings: {e}")

    def _start_periodic_recovery(self, current_balance: Decimal):
        self.periodic_recovery_active = True
        self.periodic_recovery_spins_done = 0
        self.periodic_payout_current = Decimal(self.periodic_payout_min)
        self.recovery_spent = Decimal("0")
        self._log(f"[{self.bot_id}] ▶ Periodic recovery start (interval={self.periodic_trigger_interval}, max_spins={self.periodic_recovery_max_spins}) loss_total={self.loss_total:.8f}")

    def _stop_periodic_recovery(self, reason: str):
        self._log(f"[{self.bot_id}] ▶ Periodic recovery stop: {reason} (spins={self.periodic_recovery_spins_done}, spent={self.recovery_spent:.8f})")
        self.periodic_recovery_active = False
        self.periodic_recovery_spins_done = 0
        self.recovery_spent = Decimal("0")

    def _next_periodic_payout(self):
        p = self.periodic_payout_current
        p += Decimal(1)
        if p > self.periodic_payout_max:
            p = self.periodic_payout_min
        self.periodic_payout_current = p
        return p

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
        self._log(f"[{self.bot_id}] ▶ Старт баланс={current_balance:.8f}")
        if self.initial_bank is None:
            self.initial_bank = current_balance
        if self.last_successful_bank is None:
            self.last_successful_bank = self.initial_bank
        self.balance_at_cycle_start = current_balance

        while self.is_running:
            while self.paused and self.is_running:
                time.sleep(0.1)

            self.fetch_settings_if_needed()
            current_balance = self.get_current_balance()

            if not self.periodic_recovery_active and not self.recover66_active:
                if self.spin_count > 0 and (self.spin_count % self.periodic_trigger_interval == 0):
                    self._start_periodic_recovery(current_balance)

            if self.periodic_recovery_active:
                payout = self.periodic_payout_current
            else:
                try:
                    payout = self.strategy.next_payout()
                except Exception as e:
                    self._log(f"[{self.bot_id}] Strategy error: {e}")
                    time.sleep(1)
                    continue

            wrap_event = False
            if (not self.periodic_recovery_active) and self.strategy and hasattr(self.strategy, "max_payout"):
                try:
                    if self._prev_payout is not None and Decimal(self._prev_payout) == self.strategy.max_payout and payout == self.strategy.start_payout:
                        wrap_event = True
                        self.payout_wraps += 1
                        self._log(f"[{self.bot_id}] [WRAP] max→reset (cycles={self.payout_wraps})")
                except Exception:
                    pass
            self._prev_payout = payout

            try:
                chance_decimal = (Decimal("100") / payout)
            except Exception:
                chance_decimal = Decimal("99.99")
            if chance_decimal < MIN_API_CHANCE:
                chance_decimal = MIN_API_CHANCE
            if chance_decimal > MAX_API_CHANCE:
                chance_decimal = MAX_API_CHANCE

            in_recover66 = False
            in_periodic = False

            # Wrap recovery: 66% покрытие fixed_drawdown и cycle_loss (как было)
            if self.recover66_active and not self.periodic_recovery_active:
                fixed_drawdown = Decimal("0")
                if self.bank_fixed_at_trigger is not None:
                    fixed_drawdown = self.bank_fixed_at_trigger - current_balance
                    if fixed_drawdown < 0:
                        fixed_drawdown = Decimal("0")
                target_profit = fixed_drawdown * Decimal("0.66") + self.cycle_loss * Decimal("0.66")
                bet = compute_bet_for_target_profit(
                    payout, target_profit,
                    self.min_bet or Decimal("0.001"),
                    self.config.max_bet_limit, current_balance,
                    house_edge_frac=self.house_edge_frac
                )
                in_recover66 = True

            # Периодическое восстановление (как было)
            elif self.periodic_recovery_active:
                target_profit = self.loss_total * Decimal("0.66") + self.recovery_spent
                bet = compute_bet_for_target_profit(
                    payout, target_profit,
                    self.min_bet or Decimal("0.001"),
                    self.config.max_bet_limit, current_balance,
                    house_edge_frac=self.house_edge_frac
                )
                in_periodic = True

            else:
                # ОСНОВНАЯ СТРАТЕГИЯ: ставка для покрытия всего убытка за серию (loss_total)
                target_profit = self.loss_total
                bet = compute_bet_for_target_profit(
                    payout, target_profit,
                    self.min_bet or Decimal("0.001"),
                    self.config.max_bet_limit, current_balance,
                    house_edge_frac=self.house_edge_frac
                )

            bet = quantize_bet(bet)

            if in_periodic:
                self.recovery_spent += bet

            if bet > current_balance:
                self._log(f"[{self.bot_id}] ❌ Недостаточно средств: balance={current_balance:.8f} bet={bet:.8f}")
                break

            client_seed = self.client_seed or self.api.generate_client_seed()
            res = self.api.placebet(self.config.coin, self.config.api_key,
                                    float(bet), float(payout), True, client_seed)

            if isinstance(res, dict) and res.get("error"):
                self._log(f"[{self.bot_id}] API error: {res.get('error')}")
                time.sleep(1)
                if in_periodic:
                    try:
                        self.recovery_spent = max(Decimal("0"), self.recovery_spent - bet)
                    except:
                        pass
                continue

            profit = safe_decimal(res.get("Profit", "0"))
            new_balance = safe_decimal(res.get("Balance", current_balance))
            roll_val = res.get("Roll", None)
            roll_str = f"{roll_val:.10f}" if isinstance(roll_val, float) else ("n/a" if roll_val is None else str(roll_val))
            win = profit > 0

            if win:
                prev_cycle_loss = self.cycle_loss
                self.cycle_loss = Decimal("0")
                self.last_spin_was_loss = False
                if not in_periodic and not in_recover66:
                    # так как основная стратегия покрывает loss_total, при WIN сбрасываем серию
                    self.loss_total = Decimal("0")
            else:
                self.cycle_loss += bet
                self.loss_total += bet
                self.last_spin_was_loss = True

            if win:
                self.stats["wins"] += 1
                self.stats["profit"] += profit
                self.stats["current_streak"] = max(0, self.stats["current_streak"] + 1)
                self.loss_sum = Decimal("0")
                self.streak = 0
                if self.last_successful_bank is None or new_balance > self.last_successful_bank:
                    self.last_successful_bank = new_balance

                if in_recover66:
                    pre_loss = self.cycle_loss
                    self.cycle_loss = max(Decimal("0"), self.cycle_loss * Decimal("0.34"))
                    fixed_drawdown = Decimal("0")
                    if self.bank_fixed_at_trigger is not None:
                        fixed_drawdown = self.bank_fixed_at_trigger - new_balance
                        if fixed_drawdown < 0:
                            fixed_drawdown = Decimal("0")
                    self.recover66_wins_done += 1
                    self.recover66_last_info = (
                        f"66% WIN {self.recover66_wins_done}/3, cycle_loss {pre_loss:.8f}→{self.cycle_loss:.8f}, fixed_dd={fixed_drawdown:.8f}"
                    )
                    if self.recover66_wins_done >= self.recover66_wins_target:
                        self.recover66_active = False
                        self.recover66_wins_done = 0
                        self.bank_fixed_at_trigger = None
                        self.recover66_last_info = "66% mode complete → back to linear"
                else:
                    if prev_cycle_loss and prev_cycle_loss > 0 and not self.periodic_recovery_active:
                        self._log(f"[{self.bot_id}] ℹ WIN → cycle_loss reset {prev_cycle_loss:.8f}→0")

                if in_periodic:
                    self.loss_total = Decimal("0")
                    self._stop_periodic_recovery("WIN achieved")
                    try:
                        self.strategy.reset()
                    except:
                        pass
                    self.balance_at_cycle_start = new_balance
                    self.cycle_loss = Decimal("0")
                    self.last_spin_was_loss = False

                if self.stop_on_win:
                    self.paused = True

                prefix = "[WIN-PR]" if in_periodic else ("[WIN-66%]" if in_recover66 else "[WIN]")
                self._log(f"{prefix} spin {self.spin_count + 1} payout={int(payout)} roll={roll_str} bet={bet:.8f} profit={profit:.8f}")
            else:
                self.stats["losses"] += 1
                self.stats["current_streak"] = min(0, self.stats["current_streak"] - 1)
                self.loss_sum += bet
                self.streak += 1
                if self.loss_sum > self.stats["max_loss_sum"]:
                    self.stats["max_loss_sum"] = self.loss_sum
                if bet > self.stats["max_bet"]:
                    self.stats["max_bet"] = bet

                prefix = "[LOSS-PR]" if self.periodic_recovery_active else ("[LOSS-66%]" if self.recover66_active else "[LOSS]")
                self._log(f"{prefix} spin {self.spin_count + 1} payout={int(payout)} roll={roll_str} bet={bet:.8f} cycle_loss={self.cycle_loss:.8f} loss_total={self.loss_total:.8f}")

            if self.periodic_recovery_active:
                self.periodic_recovery_spins_done += 1
                self.periodic_payout_current = self._next_periodic_payout()
                if self.periodic_recovery_spins_done >= self.periodic_recovery_max_spins:
                    self._stop_periodic_recovery("max 100 spins reached without WIN")

            self.stats["total_bets"] += 1
            self.stats["total_wagered"] += bet
            self.profit_global = new_balance - (self.initial_bank if self.initial_bank is not None else Decimal("0"))
            self._stats()
            self._bank(new_balance)

            if wrap_event:
                try:
                    cycle_result = new_balance - (self.balance_at_cycle_start if self.balance_at_cycle_start is not None else new_balance)
                    ended_with_loss = self.last_spin_was_loss
                    if cycle_result < 0 and ended_with_loss and not self.periodic_recovery_active:
                        self.recover66_active = True
                        self.recover66_wins_done = 0
                        self.bank_fixed_at_trigger = self.balance_at_cycle_start
                        self.recover66_last_info = (
                            f"66% start: cycle_result={cycle_result:.8f}, cycle_loss={self.cycle_loss:.8f}, bank_fixed={self.bank_fixed_at_trigger:.8f}"
                        )
                        self._log(f"[{self.bot_id}] ▶ 66% mode start: cycle −, last spin LOSS, cycle_loss={self.cycle_loss:.8f}, bank_fixed={self.bank_fixed_at_trigger:.8f}")
                    else:
                        if self.recover66_active:
                            self.recover66_active = False
                            self.recover66_wins_done = 0
                            self.bank_fixed_at_trigger = None
                        if self.cycle_loss > 0:
                            self._log(f"[{self.bot_id}] ℹ cycle end: result={cycle_result:.8f} → cycle_loss reset {self.cycle_loss:.8f}→0")
                        self.cycle_loss = Decimal("0")
                    self.balance_at_cycle_start = new_balance
                    self.last_spin_was_loss = False
                except Exception as e:
                    self._log(f"[{self.bot_id}] ⚠ cycle wrap handling error: {e}")

            if self.manager_ref:
                try:
                    self.manager_ref.check_global_take_profit()
                except:
                    pass

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

        self.coin_box.set("USDT")
        self.bet_entry.insert(0, "0.001")
        self.enforced_min_entry.insert(0, "0.001")
        self.maxbet_entry.insert(0, "1.0")
        self.speed_box.set(50)
        self.minbet_refresh_spin.set(30)
        self.target_min_bets_spin.set(10)
        self.min_payout_entry.insert(0, "1000")
        self.max_payout_entry.insert(0, "9999")

        bank_frame = ttk.LabelFrame(right, text="Bank", padding=6)
        bank_frame.pack(fill="x", pady=(0,6))
        self.initial_bank_lbl = ttk.Label(bank_frame, text="Initial: 0.00000000 USDT"); self.initial_bank_lbl.pack(anchor="w")
        self.last_bank_lbl = ttk.Label(bank_frame, text="Last successful: 0.00000000 USDT"); self.last_bank_lbl.pack(anchor="w")
        self.current_bank_lbl = ttk.Label(bank_frame, text="Current: 0.00000000 USDT"); self.current_bank_lbl.pack(anchor="w")
        self.cycle_loss_lbl = ttk.Label(bank_frame, text="Cycle loss: 0.00000000 USDT"); self.cycle_loss_lbl.pack(anchor="w")
        self.periodic_lbl = ttk.Label(bank_frame, text="Periodic recovery: inactive")
        self.periodic_lbl.pack(anchor="w")
        self.recover_lbl = ttk.Label(bank_frame, text="Wrap recovery 66%: inactive")
        self.recover_lbl.pack(anchor="w")

        ttk.Label(right, text=f"{self.bot_name} Last 200 results").pack(anchor="w")
        self.log_text = scrolledtext.ScrolledText(right, height=20, state="normal", wrap="none")
        self.log_text.pack(fill="both", expand=True)
        self.log_text.tag_config("win", foreground="green")
        self.log_text.tag_config("loss", foreground="red")
        self.log_text.tag_config("info", foreground="blue")
        self._bet_lines = deque(maxlen=200)

        os.makedirs("logs", exist_ok=True)
        safe_name = self.bot_name.replace("/", "_").replace("\\", "_")
        self.log_file_path = os.path.join("logs", f"{safe_name}.txt")

        self.bot = None
        self.bot_thread = None

    def _file_log(self, msg: str):
        try:
            ts = time.strftime("%Y-%m-%d %H:%M:%S")
            with open(self.log_file_path, "a", encoding="utf-8") as f:
                f.write(f"{ts} {msg}\n")
        except Exception as e:
            print(f"[{self.bot_name}] File log error: {e}")

    def _render_bet_log(self):
        try:
            self.log_text.configure(state="normal")
            self.log_text.delete("1.0", "end")
            for line, tag in self._bet_lines:
                if tag:
                    self.log_text.insert("end", line + "\n", tag)
                else:
                    self.log_text.insert("end", line + "\n")
            self.log_text.see("end")
            self.log_text.configure(state="normal")
        except Exception as e:
            print(f"[{self.bot_name}] UI log render error: {e}")

    def log_bet(self, raw_line: str):
        ll = raw_line.lower()
        tag = "info"
        if ll.startswith("[win"):
            tag = "win"
        elif ll.startswith("[loss"):
            tag = "loss"
        self._bet_lines.append((raw_line, tag))
        self._render_bet_log()

    def log(self, msg):
        ts = time.strftime("%H:%M:%S")
        line = f"{ts} [{self.bot_name}] {msg}"
        print(line)
        self._file_log(f"[{self.bot_name}] {msg}")
        self.log_bet(msg)

    def _parse_decimal(self, value, default):
        try:
            if value is None:
                return Decimal(default)
            s = str(value).strip()
            if s == "":
                return Decimal(default)
            return Decimal(s)
        except (InvalidOperation, ValueError):
            return Decimal(default)

    def _parse_int(self, value, default):
        try:
            if value is None:
                return int(default)
            s = str(value).strip()
            if s == "":
                return int(default)
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

        try:
            min_payout = Decimal(str(self.min_payout_entry.get()).strip())
        except Exception:
            min_payout = Decimal("1000")
        try:
            max_payout = Decimal(str(self.max_payout_entry.get()).strip())
        except Exception:
            max_payout = Decimal("9999")
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

        def log_cb(msg: str):
            self.manager.enqueue(('log', bot_id, msg))

        bank_cb = lambda stats: self.manager.enqueue(('bank', bot_id, stats))
        stats_cb = lambda stats: self.manager.enqueue(('stats', bot_id, stats))

        try:
            self.bot = CryptoGamesBot(bot_id, api_client, cfg,
                                      log_cb, bank_cb, stats_cb,
                                      pause_on_fail=pause_on_fail,
                                      stop_on_win=stop_on_win,
                                      executor=self.manager.executor)

            def linear_factory():
                return LinearPayoutStrategy(start_payout=min_payout, max_payout=max_payout)

            self.bot.set_strategy_factories([linear_factory])
            self.bot.set_strategy(linear_factory())

            seed = self.seed_entry.get().strip()
            if seed:
                self.bot.client_seed = seed

            self.bot.manager_ref = self.manager

            self.start_btn.config(state="disabled")
            self.pause_btn.config(state="normal")
            self.stop_btn.config(state="normal")
            self.bot_thread = threading.Thread(target=self.bot.start, daemon=True)
            self.bot_thread.start()
            self.manager.register_bot(self.bot, self)
            self.manager.enqueue(('log', bot_id,
                                  f"Запущен payout {int(min_payout)}..{int(max_payout)}; periodic recovery: interval=200, range=100..200, max_spins=100"))
        except Exception as e:
            self.manager.enqueue(('log', bot_id, f"Ошибка запуска: {e}"))
            self.manager.enqueue(('trace', bot_id, traceback.format_exc()))

    def toggle_pause(self):
        if not self.bot:
            return
        paused = self.bot.pause_toggle()
        self.pause_btn.config(text="Resume" if paused else "Pause")
        self.manager.enqueue(('log', self.bot_name, "Paused" if paused else "Resumed"))

    def stop_bot(self):
        if self.bot:
            try:
                self.bot.stop()
            except Exception as e:
                self.manager.enqueue(('log', self.bot_name, f"Ошибка остановки: {e}"))
            self.manager.unregister_bot(self.bot.bot_id)
        self.start_btn.config(state="normal")
        self.pause_btn.config(state="disabled", text="Pause")
        self.stop_btn.config(state="disabled")
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
            cycle_loss = safe_decimal(stats.get("cycle_loss", "0"))
            periodic_active = bool(stats.get("periodic_active", False))
            periodic_spins = int(stats.get("periodic_spins", 0))
            recovery_spent = safe_decimal(stats.get("recovery_spent", "0"))
            loss_total = safe_decimal(stats.get("loss_total", "0"))
            recover66_active = bool(stats.get("recover66_active", False))
            recover66_wins_done = int(stats.get("recover66_wins_done", 0))
            rec66_info = stats.get("recover66_info", "")
        except Exception:
            initial = last = current = Decimal("0")
            cycle_loss = Decimal("0")
            periodic_active = False
            periodic_spins = 0
            recovery_spent = Decimal("0")
            loss_total = Decimal("0")
            recover66_active = False
            recover66_wins_done = 0
            rec66_info = ""

        def _upd():
            self.initial_bank_lbl.config(text=f"Initial: {initial:.8f} {coin}")
            self.last_bank_lbl.config(text=f"Last successful: {last:.8f} {coin}")
            self.current_bank_lbl.config(text=f"Current: {current:.8f} {coin}")
            self.cycle_loss_lbl.config(text=f"Cycle loss: {cycle_loss:.8f} {coin}")
            col = "darkgreen" if current >= initial else "red"
            self.current_bank_lbl.config(foreground=col)
            self.periodic_lbl.config(text=f"Periodic recovery: {'active' if periodic_active else 'inactive'} (spins={periodic_spins}, spent={recovery_spent:.8f}, loss_total={loss_total:.8f})")
            status = "active" if recover66_active else "inactive"
            info = rec66_info or ""
            self.recover_lbl.config(text=f"Wrap recovery 66%: {status} (wins={recover66_wins_done}/3) {info}")
        try:
            self.frame.after(0, _upd)
        except:
            _upd()

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
            self.all_banks[bot_id := bot.bot_id] = {"current_bank": curr, "profit_global": prof, "initial_bank": init}
        self._update_aggregate_label()

    def unregister_bot(self, bot_id: str):
        with self.lock:
            self.active_bots.pop(bot_id, None)
            self.all_banks.pop(bot_id, None)
        self._update_aggregate_label()

    def enqueue(self, item_tuple):
        try:
            self.ui_queue.put_nowait(item_tuple)
        except queue.Full:
            pass

    def _process_ui_queue(self):
        processed = 0
        max_per_cycle = 600
        while processed < max_per_cycle:
            try:
                typ, bot_id, payload = self.ui_queue.get_nowait()
            except queue.Empty:
                break
            if typ == 'log':
                tab = self.bot_tabs.get(bot_id)
                if tab:
                    try:
                        tab.log(payload)
                    except Exception:
                        pass
            elif typ == 'trace':
                print(payload)
            elif typ == 'bank':
                stats = payload
                try:
                    curr = safe_decimal(stats.get("current_bank"))
                    init = safe_decimal(stats.get("initial_bank"))
                    prof = safe_decimal(stats.get("profit_global"))
                    if init <= 0:
                        init = curr
                    with self.lock:
                        self.all_banks[bot_id] = {"current_bank": curr, "profit_global": prof, "initial_bank": init}
                    tab = self.bot_tabs.get(bot_id)
                    if tab:
                        tab.update_bank_ui(stats)
                    self._update_aggregate_label()
                except Exception:
                    pass
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
        except:
            pass

    def _aggregate_initial_and_current(self):
        with self.lock:
            total_current = Decimal("0")
            total_initial = Decimal("0")
            for v in self.all_banks.values():
                curr = safe_decimal(v.get("current_bank"))
                init = safe_decimal(v.get("initial_bank"))
                if init <= 0:
                    init = curr
                total_current += curr
                total_initial += init
        return total_initial, total_current

    def _parse_tp_percent(self):
        try:
            p = Decimal(str(self.global_take_profit_percent_var.get()).strip())
            if p <= 0:
                return None
            return p
        except Exception:
            return None

    def check_global_take_profit(self, force=False):
        if not self.global_take_profit_enabled.get():
            return
        tp_percent = self._parse_tp_percent()
        if tp_percent is None:
            return
        total_initial, total_current = self._aggregate_initial_and_current()
        if total_initial <= 0:
            return
        target = total_initial * (Decimal("1") + tp_percent / Decimal("100"))
        if total_current >= target:
            if not self.global_tp_active or force:
                self._trigger_global_tp(total_current, total_initial, tp_percent)

    def _trigger_global_tp(self, total_current: Decimal, total_initial: Decimal, tp_percent: Decimal):
        self.global_tp_active = True
        growth = (total_current - total_initial) * Decimal("100") / total_initial
        print(f"[Manager] Global TP triggered: growth={growth:.2f}% target={tp_percent:.2f}% pause 5s")
        with self.lock:
            self.tp_new_initials = {}
            for bot_id, rec in self.all_banks.items():
                self.tp_new_initials[bot_id] = safe_decimal(rec.get("current_bank"))
            for bot in self.active_bots.values():
                bot.paused = True
                bot._log(f"[{bot.bot_id}] Global TP pause 5s (growth={growth:.2f}%)")
        self.root.after(5000, self._resume_after_tp)

    def _resume_after_tp(self):
        with self.lock:
            for bot_id, bot in self.active_bots.items():
                new_initial = self.tp_new_initials.get(bot_id, None)
                if new_initial is None or new_initial <= 0:
                    new_initial = safe_decimal(self.all_banks.get(bot_id, {}).get("current_bank"))
                rec = self.all_banks.get(bot_id, {}) or {}
                rec["initial_bank"] = new_initial
                rec["current_bank"] = new_initial
                self.all_banks[bot_id] = rec
                bot.restart_after_tp(new_initial)
                bot.paused = False
            self.global_tp_active = False
            self.tp_new_initials = {}
        print("[Manager] Global TP resume done")

    def stop_all_bots(self):
        with self.lock:
            bots = list(self.active_bots.values())
        for b in bots:
            try:
                b.stop()
            except Exception:
                pass
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