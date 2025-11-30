#!/usr/bin/env python3
# Crypto.Games multi-bot GUI — multithreaded UI queue
# Обновление стратегии: ловим двойные выигрыши (Double-Press) + глобальный стоп‑профит/стоп‑лосс.
#
# ДОПОЛНЕНО: Стратегия восстановления (Recovery) с общим S_ref и настраиваемыми параметрами
# - Общий S_ref = максимальный last_successful_bank среди активных ботов на момент триггера Recovery.
# - Включение Recovery: когда просадка от общей опоры достигает порога (по умолчанию 20%).
#   drawdown% = ((N*shared_S_ref - Σ current_banks) / (N*shared_S_ref)) * 100, где N — число активных ботов.
# - Каждый бот восстанавливает свой текущий банк до shared_S_ref (без 105%).
# - Ставка рассчитывается от целевого профита на спин:
#     target_profit_spin = min(recovery_percent * shared_S_ref / N, recovery_usdt, R),
#     где R = max(0, shared_S_ref - current_bank_бота).
# - payout в Recovery: настраиваемый диапазон [Recovery Min payout .. Recovery Max payout], старт с Min.
#   На LOSS: payout += 1, не превышая Max. На WIN: сброс на Min.
# - Double-Press отключён во время Recovery.
# - При успешном окончании Recovery обычная стратегия сбрасывается к началу (reset scan payout).
#
# ДОПОЛНЕНО: Ручная установка триггера просадки (Recovery)
# - Вверху UI добавлены поля:
#   * Recovery DD % — порог просадки в процентах.
#   * Recovery DD USDT — порог просадки в абсолюте (USDT).
# - Триггер срабатывает, если выполнено ЛИБО условие по % (>=), ЛИБО по USDT (>=).
#
# ДОПОЛНЕНО: Глобальное завершение Recovery
# - Если хотя бы один бот достиг цели (его банк ≥ shared_S_ref), менеджер немедленно
#   завершает Recovery для всех ботов и сбрасывает обычную стратегию на начало у всех ботов.
#
# ДОПОЛНЕНО: Задержки без блокировки UI
# - Старт всех ботов по очереди: 5 секунд между каждым (root.after).
# - Возврат к обычной стратегии после Recovery: 5 секунд между возобновлениями (root.after).
#
# ДОПОЛНЕНО: При завершении Recovery сбрасываем общий банк каждого бота (initial_bank=current, last_successful_bank=current, profit_global=0) чтобы избежать больших ставок.
#
# Требования: requests, tkinter (стандартный модуль), Python 3.10+

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
from typing import Optional

getcontext().prec = 40

API_BASE = "https://api.crypto.games/v1"

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
    # Recovery settings (UI-driven)
    recovery_min_payout: int = 50
    recovery_max_payout: int = 1000
    recovery_trigger_dd_percent: Decimal = Decimal("20")
    recovery_percent_per_win: Decimal = Decimal("21")
    recovery_usdt_per_win: Decimal = Decimal("0")
    use_shared_s_ref: bool = True

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

class LinearPayoutStrategy:
    def __init__(self, start_payout=Decimal("100"), max_payout=Decimal("9999")):
        self.start_payout = Decimal(start_payout)
        self.max_payout = Decimal(max_payout)
        self.current_payout = Decimal(start_payout)

    def reset(self):
        self.current_payout = Decimal(self.start_payout)

    def next_payout_and_bet(self, state):
        payout = self.current_payout
        nxt = payout + Decimal(1)
        if nxt > self.max_payout:
            nxt = Decimal(self.start_payout)
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

        self.press_active = False
        self.press_left = 0
        self.press_payout = None
        self.press_bet = Decimal("0.1")
        self.enable_highroll_99 = False

        self.recovery_active = False
        self.recovery_payout = Decimal("50")
        self.recovery_min_payout = Decimal(self.config.recovery_min_payout)
        self.recovery_max_payout = Decimal(self.config.recovery_max_payout)
        self.recovery_shared_S_ref: Optional[Decimal] = None
        self.recovery_divisor: int = 1
        self.recovery_target_end: Optional[Decimal] = None

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
        try:
            self.log_cb(msg)
        except Exception:
            print(f"[{self.bot_id}] {msg}")

    def _push_bank_payload(self, bal: Decimal):
        if self.initial_bank is None:
            self.initial_bank = bal
        data = {
            "initial_bank": self.initial_bank,
            "last_successful_bank": self.last_successful_bank if self.last_successful_bank is not None else self.initial_bank,
            "current_bank": bal,
            "profit_global": self.profit_global,
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
                self._log(f"[{self.bot_id}] 🔎 Settings: MinBet={self.min_bet} Edge={edge_raw}")
            except Exception as e:
                self._log(f"[{self.bot_id}] ⚠️ Failed parsing settings: {e}")

    def enter_recovery(self, shared_S_ref: Decimal, divisor: int):
        try:
            sref = safe_decimal(shared_S_ref, "0")
            if sref <= 0:
                return
            self.recovery_shared_S_ref = sref
            self.recovery_divisor = max(1, int(divisor))
            self.recovery_target_end = sref
            self.recovery_payout = Decimal(self.recovery_min_payout)
            self.press_active = False
            self.press_left = 0
            self.press_payout = None
            self.recovery_active = True
            self._log(f"[{self.bot_id}] [RECOVERY] ▶ Start(shared): S_ref={self.recovery_shared_S_ref:.8f} divisor={self.recovery_divisor} target_end={self.recovery_target_end:.8f} payout_start={int(self.recovery_min_payout)}")
        except Exception as e:
            self._log(f"[{self.bot_id}] [RECOVERY] enter error: {e}")

    def _maybe_exit_recovery(self, current_balance: Decimal):
        if self.recovery_active and self.recovery_target_end is not None:
            if current_balance >= self.recovery_target_end:
                try:
                    if self.manager_ref and hasattr(self.manager_ref, "force_end_recovery"):
                        self.manager_ref.force_end_recovery(initiator_id=self.bot_id)
                except Exception:
                    pass
                self.recovery_active = False
                if self.strategy:
                    try:
                        self.strategy.reset()
                        self._log(f"[{self.bot_id}] [RECOVERY] ✅ Completed → reset base strategy to start")
                    except Exception:
                        self._log(f"[{self.bot_id}] [RECOVERY] ✅ Completed (base strategy reset failed)")
                else:
                    self._log(f"[{self.bot_id}] [RECOVERY] ✅ Completed")

    def _activate_press(self, payout: Decimal, reason: str):
        self.press_active = True
        self.press_left = 2
        self.press_payout = Decimal(payout)
        self._log(f"[{self.bot_id}] ▶ Press start: payout={int(self.press_payout)} bet={self.press_bet:.6f} (2 spins) reason={reason}")

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
        self._log(f"[{self.bot_id}] Старт баланс={current_balance:.8f}")
        if self.initial_bank is None:
            self.initial_bank = current_balance
        if self.last_successful_bank is None:
            self.last_successful_bank = self.initial_bank

        while self.is_running:
            while self.paused and self.is_running:
                time.sleep(0.1)

            self.fetch_settings_if_needed()
            current_balance = self.get_current_balance()

            mode = "BASE"
            bet = Decimal("0")
            payout = Decimal("50")

            if self.recovery_active and self.recovery_shared_S_ref and self.recovery_target_end:
                mode = "RECOVERY"
                payout = Decimal(self.recovery_payout)

                R = self.recovery_target_end - current_balance
                if R <= 0:
                    self._maybe_exit_recovery(current_balance)
                    continue

                target_from_percent = (self.config.recovery_percent_per_win / Decimal("100")) * self.recovery_shared_S_ref / Decimal(self.recovery_divisor)
                target_from_usdt = self.config.recovery_usdt_per_win / Decimal(max(1, self.recovery_divisor)) if self.config.recovery_usdt_per_win > 0 else Decimal("0")
                target_unit = target_from_usdt if target_from_usdt > 0 else target_from_percent
                target_profit = target_unit if target_unit <= R else R

                denom = payout - Decimal("1")
                if denom <= 0:
                    denom = Decimal("1")
                bet = target_profit / denom

                bet = max(bet, self.config.min_bet_enforced, self.min_bet or Decimal("0.001"))
                if self.config.max_bet_limit and bet > self.config.max_bet_limit:
                    bet = self.config.max_bet_limit
                if bet > current_balance:
                    bet = current_balance

            elif self.press_active and self.press_left > 0 and self.press_payout is not None:
                payout = Decimal(self.press_payout)
                bet = Decimal(self.press_bet)
                mode = "PRESS"
            else:
                try:
                    payout, _, _, _ = self.strategy.next_payout_and_bet({"min_bet": self.min_bet})
                except Exception as e:
                    self._log(f"[{self.bot_id}] Strategy error: {e}")
                    time.sleep(1)
                    continue
                bet = Decimal(max(self.config.base_bet, self.config.min_bet_enforced))
                mode = "BASE"

            if mode != "RECOVERY" and self.strategy and hasattr(self.strategy, "max_payout"):
                try:
                    if self._prev_payout is not None and Decimal(self._prev_payout) == self.strategy.max_payout and payout == self.strategy.start_payout:
                        self.payout_wraps += 1
                        self._log(f"[{self.bot_id}] [WRAP] max→reset count={self.payout_wraps}")
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

            bet = quantize_bet(bet)

            if bet > current_balance:
                self._log(f"[{self.bot_id}] ❌ Недостаточно средств: balance={current_balance:.8f} bet={bet:.8f}")
                break

            client_seed = self.client_seed or self.api.generate_client_seed()
            res = self.api.placebet(self.config.coin, self.config.api_key,
                                    float(bet), float(payout), True, client_seed)

            if isinstance(res, dict) and res.get("error"):
                self._log(f"[{self.bot_id}] API error: {res.get('error')}")
                time.sleep(1)
                continue

            profit = safe_decimal(res.get("Profit", "0"))
            new_balance = safe_decimal(res.get("Balance", current_balance))
            roll_val = res.get("Roll", None)
            roll_str = f"{roll_val:.10f}" if isinstance(roll_val, float) else ("n/a" if roll_val is None else str(roll_val))
            win = profit > 0

            if mode == "RECOVERY":
                prefix = "[WIN-RECOVERY]" if win else "[LOSS-RECOVERY]"
            else:
                prefix = "[WIN-PRESS]" if (win and mode == "PRESS") else ("[WIN]" if win else ("[LOSS-PRESS]" if mode == "PRESS" else "[LOSS]"))

            if win:
                self.stats["wins"] += 1
                self.stats["profit"] += profit
                self.stats["current_streak"] = max(0, self.stats["current_streak"] + 1)
                self.loss_sum = Decimal("0")
                self.streak = 0
                if self.last_successful_bank is None or new_balance > self.last_successful_bank:
                    self.last_successful_bank = new_balance
                if self.stop_on_win and mode != "RECOVERY":
                    self.paused = True
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
                self._log(f"{prefix} spin {self.spin_count + 1} payout={int(payout)} roll={roll_str} bet={bet:.8f}")

            self.stats["total_bets"] += 1
            self.stats["total_wagered"] += bet
            self.profit_global = new_balance - (self.initial_bank if self.initial_bank is not None else Decimal("0"))
            self._stats()
            self._bank(new_balance)

            if mode == "RECOVERY":
                if win:
                    # На WIN — сброс на минимальный payout
                    self.recovery_payout = Decimal(self.recovery_min_payout)
                else:
                    # На LOSS — увеличиваем payout на 1
                    try:
                        np = int(self.recovery_payout) + 1
                        # Если достигли или превысили Recovery Max payout — СБРОС НА МИНИМАЛЬНЫЙ (wrap)
                        if np > int(self.recovery_max_payout) or int(self.recovery_payout) >= int(self.recovery_max_payout):
                            np = int(self.recovery_min_payout)
                        self.recovery_payout = Decimal(np)
                    except Exception:
                        self.recovery_payout = Decimal(self.recovery_min_payout)
                # Проверка выхода / глобального завершения
                self._maybe_exit_recovery(new_balance)

            elif mode == "PRESS":
                if win:
                    self.press_active = False
                    self.press_left = 0
                    self.press_payout = None
                else:
                    self.press_left -= 1
                    if self.press_left <= 0:
                        self.press_active = False
                        self.press_payout = None
            else:
                if win:
                    if self.enable_highroll_99 and (roll_val is not None):
                        try:
                            if Decimal(str(roll_val)) >= Decimal("99.000"):
                                self._activate_press(Decimal("100"), reason="highroll99")
                            else:
                                if Decimal("5") <= Decimal(payout) <= Decimal("8") and Decimal(str(roll_val)) >= Decimal("90.000"):
                                    self._activate_press(Decimal("10"), reason="win-5-8-roll>=90")
                        except Exception:
                            pass
                    else:
                        try:
                            if Decimal("5") <= Decimal(payout) <= Decimal("8") and (roll_val is not None) and Decimal(str(roll_val)) >= Decimal("90.000"):
                                self._activate_press(Decimal("10"), reason="win-5-8-roll>=90")
                        except Exception:
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
        self.max_bet_entry = ttk.Entry(left, width=12)
        self.speed_box = ttk.Spinbox(left, from_=10, to=5000, increment=10, width=8)
        self.minbet_refresh_spin = ttk.Spinbox(left, from_=5, to=600, increment=5, width=8)
        self.target_min_bets_spin = ttk.Spinbox(left, from_=1, to=1000, increment=1, width=6)
        self.min_payout_entry = ttk.Entry(left, width=12)
        self.max_payout_entry = ttk.Entry(left, width=12)

        self.recovery_min_payout_entry = ttk.Entry(left, width=12)
        self.recovery_max_payout_entry = ttk.Entry(left, width=12)
        self.recovery_percent_entry = ttk.Entry(left, width=12)
        self.recovery_usdt_entry = ttk.Entry(left, width=12)

        self.pause_on_fail_var = tk.BooleanVar(value=False)
        self.stop_on_win_var = tk.BooleanVar(value=False)
        self.seed_entry = ttk.Entry(left, width=20)

        self.enable_highroll_var = tk.BooleanVar(value=False)

        self.start_btn = ttk.Button(left, text="Start", command=self.start_bot)
        self.pause_btn = ttk.Button(left, text="Pause", command=self.toggle_pause, state="disabled")
        self.stop_btn = ttk.Button(left, text="Stop", command=self.stop_bot, state="disabled")
        self.seed_btn = ttk.Button(left, text="Gen Seed", command=self.generate_seed)

        ttk.Label(left, text="API Key:").grid(row=0,column=0,sticky="w"); self.api_entry.grid(row=0,column=1,padx=4)
        ttk.Label(left, text="Coin:").grid(row=1,column=0,sticky="w"); self.coin_box.grid(row=1,column=1,padx=4)
        ttk.Label(left, text="Base bet:").grid(row=2,column=0,sticky="w"); self.bet_entry.grid(row=2,column=1,padx=4)
        ttk.Label(left, text="Enforced min:").grid(row=3,column=0,sticky="w"); self.enforced_min_entry.grid(row=3,column=1,padx=4)
        ttk.Label(left, text="Max bet limit:").grid(row=4,column=0,sticky="w"); self.max_bet_entry.grid(row=4,column=1,padx=4)
        ttk.Label(left, text="Speed ms:").grid(row=5,column=0,sticky="w"); self.speed_box.grid(row=5,column=1,padx=4)
        ttk.Label(left, text="Min settings refresh s:").grid(row=6,column=0,sticky="w"); self.minbet_refresh_spin.grid(row=6,column=1,padx=4)
        ttk.Label(left, text="Target M:").grid(row=7,column=0,sticky="w"); self.target_min_bets_spin.grid(row=7,column=1,padx=4)
        ttk.Label(left, text="Min payout:").grid(row=8,column=0,sticky="w"); self.min_payout_entry.grid(row=8,column=1,padx=4)
        ttk.Label(left, text="Max payout:").grid(row=9,column=0,sticky="w"); self.max_payout_entry.grid(row=9,column=1,padx=4)

        ttk.Label(left, text="Recovery Min payout:").grid(row=10,column=0,sticky="w"); self.recovery_min_payout_entry.grid(row=10,column=1,padx=4)
        ttk.Label(left, text="Recovery Max payout:").grid(row=11,column=0,sticky="w"); self.recovery_max_payout_entry.grid(row=11,column=1,padx=4)
        ttk.Label(left, text="Recovery % per win:").grid(row=12,column=0,sticky="w"); self.recovery_percent_entry.grid(row=12,column=1,padx=4)
        ttk.Label(left, text="Recovery USDT per win:").grid(row=13,column=0,sticky="w"); self.recovery_usdt_entry.grid(row=13,column=1,padx=4)

        ttk.Checkbutton(left, text="Pause on FAIL", variable=self.pause_on_fail_var,
                        command=self._on_pause_on_fail_toggled).grid(row=14,column=0,columnspan=2,sticky="w")
        ttk.Checkbutton(left, text="Stop on WIN", variable=self.stop_on_win_var,
                        command=self._on_stop_on_win_toggled).grid(row=15,column=0,columnspan=2,sticky="w")

        ttk.Checkbutton(left, text="Enable HighRoll 99→payout 100 (2x @0.1)",
                        variable=self.enable_highroll_var).grid(row=16,column=0,columnspan=2,sticky="w",pady=(6,0))

        ttk.Label(left, text="Client Seed:").grid(row=17,column=0,sticky="w"); self.seed_entry.grid(row=17,column=1,padx=4)

        btnf = ttk.Frame(left); btnf.grid(row=18,column=0,columnspan=2,pady=(8,0))
        self.start_btn.pack(in_=btnf, side="left", padx=4)
        self.pause_btn.pack(in_=btnf, side="left", padx=4)
        self.stop_btn.pack(in_=btnf, side="left", padx=4)
        self.seed_btn.pack(in_=btnf, side="left", padx=4)

        bank_frame = ttk.LabelFrame(right, text="Bank", padding=6)
        bank_frame.pack(fill="x", pady=(0,6))
        self.initial_bank_lbl = ttk.Label(bank_frame, text="Initial: 0.00000000 USDT"); self.initial_bank_lbl.pack(anchor="w")
        self.last_bank_lbl = ttk.Label(bank_frame, text="Last successful: 0.00000000 USDT"); self.last_bank_lbl.pack(anchor="w")
        self.current_bank_lbl = ttk.Label(bank_frame, text="Current: 0.00000000 USDT"); self.current_bank_lbl.pack(anchor="w")

        ttk.Label(right, text=f"{self.bot_name} Last 20 results").pack(anchor="w")
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
            self.max_bet_entry.insert(0, str(initial_config.max_bet_limit))
            self.speed_box.set(initial_config.speed_ms)
            self.minbet_refresh_spin.set(initial_config.min_bet_refresh_secs)
            self.target_min_bets_spin.set(initial_config.target_min_bets_on_win)
        else:
            self.coin_box.set("USDT")
            self.bet_entry.insert(0, "0.001")
            self.enforced_min_entry.insert(0, "0.001")
            self.max_bet_entry.insert(0, "1.0")
            self.speed_box.set(50)
            self.minbet_refresh_spin.set(30)
            self.target_min_bets_spin.set(10)

        self.min_payout_entry.insert(0, "100")
        self.max_payout_entry.insert(0, "9999")
        self.recovery_min_payout_entry.insert(0, "50")
        self.recovery_max_payout_entry.insert(0, "1000")
        self.recovery_percent_entry.insert(0, "21")
        self.recovery_usdt_entry.insert(0, "0")

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
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        for line, tag in self._bet_lines:
            self.log_text.insert("end", line + "\n", (tag if tag else ()))
        self.log_text.see("end")
        self.log_text.configure(state="normal")

    def log_bet(self, raw_line: str):
        ll = raw_line.lower()
        tag = None
        if ll.startswith("[win"):
            tag = "win"
        elif ll.startswith("[loss"):
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
        cfg.max_bet_limit = self._parse_decimal(self.max_bet_entry.get(), cfg.max_bet_limit)
        cfg.speed_ms = self._parse_int(self.speed_box.get(), cfg.speed_ms)
        cfg.min_bet_refresh_secs = self._parse_int(self.minbet_refresh_spin.get(), cfg.min_bet_refresh_secs)
        cfg.target_min_bets_on_win = self._parse_int(self.target_min_bets_spin.get(), cfg.target_min_bets_on_win)

        cfg.recovery_min_payout = self._parse_int(self.recovery_min_payout_entry.get(), cfg.recovery_min_payout)
        cfg.recovery_max_payout = self._parse_int(self.recovery_max_payout_entry.get(), cfg.recovery_max_payout)
        rp = self._parse_decimal(self.recovery_percent_entry.get(), cfg.recovery_percent_per_win)
        if rp < 0:
            rp = Decimal("0")
        cfg.recovery_percent_per_win = rp
        ru = self._parse_decimal(self.recovery_usdt_entry.get(), cfg.recovery_usdt_per_win)
        if ru < 0:
            ru = Decimal("0")
        cfg.recovery_usdt_per_win = ru

        if cfg.recovery_min_payout < 2:
            cfg.recovery_min_payout = 50
        if cfg.recovery_max_payout <= cfg.recovery_min_payout:
            cfg.recovery_max_payout = cfg.recovery_min_payout + 1

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
            min_payout = Decimal("100")
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

            self.bot.enable_highroll_99 = bool(self.enable_highroll_var.get())

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
                                  f"Запущен payout {int(min_payout)}..{int(max_payout)} highroll99={self.bot.enable_highroll_99} | Recovery [{cfg.recovery_min_payout}..{cfg.recovery_max_payout}] %={cfg.recovery_percent_per_win} USDT={cfg.recovery_usdt_per_win}"))
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
        except Exception:
            initial = last = current = Decimal("0")
            coin = "USDT"

        def _upd():
            self.initial_bank_lbl.config(text=f"Initial: {initial:.8f} {coin}")
            self.last_bank_lbl.config(text=f"Last successful: {last:.8f} {coin}")
            self.current_bank_lbl.config(text=f"Current: {current:.8f} {coin}")
            col = "darkgreen" if current >= initial else "red"
            self.current_bank_lbl.config(foreground=col)
        try:
            self.frame.after(0, _upd)
        except:
            _upd()

class BotManagerApp:
    def __init__(self, ui_poll_ms: int = 100):
        self.root = tk.Tk()
        self.root.title("Crypto.Games Multi-Bot Manager (Double-Press + Recovery)")
        self.root.geometry("1200x860")
        self.bot_tabs = {}
        self.active_bots = {}
        self.all_banks = {}
        self.lock = threading.Lock()
        self.ui_queue = queue.Queue()
        max_workers = min(32, (os.cpu_count() or 4) * 5)
        self.executor = ThreadPoolExecutor(max_workers=max_workers)
        self.ui_poll_ms = ui_poll_ms

        self.global_tp_enabled = tk.BooleanVar(value=False)
        self.global_sl_enabled = tk.BooleanVar(value=False)
        self.global_tp_percent_var = tk.StringVar(value="10")
        self.global_sl_percent_var = tk.StringVar(value="10")
        self.global_stop_fired = False

        self.recovery_dd_percent_var = tk.StringVar(value="20")
        self.recovery_dd_usdt_var = tk.StringVar(value="0")
        self.recovery_global_active = False

        self._build_ui()
        self.new_bot_tab()
        self.root.after(self.ui_poll_ms, self._process_ui_queue)

    def _build_ui(self):
        top = ttk.Frame(self.root); top.pack(fill="x", padx=6, pady=6)
        self.agg_label = ttk.Label(top, text="Aggregate: Current=0.00000000 Profit=+0.00000000")
        self.agg_label.pack(side="left", padx=(4,14))

        ttk.Button(top, text="New Bot", command=self.new_bot_tab).pack(side="left")
        ttk.Button(top, text="Start All", command=self.start_all_bots).pack(side="left", padx=6)
        ttk.Button(top, text="Stop All", command=self.stop_all_bots).pack(side="left", padx=6)

        sep = ttk.Label(top, text=" | "); sep.pack(side="left", padx=6)
        ttk.Label(top, text="Global TP %:").pack(side="left", padx=(6,4))
        self.tp_entry = ttk.Entry(top, textvariable=self.global_tp_percent_var, width=6); self.tp_entry.pack(side="left", padx=2)
        ttk.Checkbutton(top, text="Enable TP", variable=self.global_tp_enabled).pack(side="left", padx=6)

        ttk.Label(top, text="Global SL %:").pack(side="left", padx=(16,4))
        self.sl_entry = ttk.Entry(top, textvariable=self.global_sl_percent_var, width=6); self.sl_entry.pack(side="left", padx=2)
        ttk.Checkbutton(top, text="Enable SL", variable=self.global_sl_enabled).pack(side="left", padx=6)

        ttk.Label(top, text=" | ").pack(side="left", padx=6)
        ttk.Label(top, text="Recovery DD %:").pack(side="left", padx=(6,4))
        self.recovery_dd_percent_entry = ttk.Entry(top, textvariable=self.recovery_dd_percent_var, width=6); self.recovery_dd_percent_entry.pack(side="left", padx=2)
        ttk.Label(top, text="Recovery DD USDT:").pack(side="left", padx=(12,4))
        self.recovery_dd_usdt_entry = ttk.Entry(top, textvariable=self.recovery_dd_usdt_var, width=10); self.recovery_dd_usdt_entry.pack(side="left", padx=2)

        self.bot_notebook = ttk.Notebook(self.root); self.bot_notebook.pack(fill="both", expand=True, padx=6, pady=(0,6))

    def new_bot_tab(self):
        idx = len(self.bot_tabs) + 1
        tab = BotTab(self.bot_notebook, self, idx)
        self.bot_tabs[tab.bot_name] = tab
        self.bot_notebook.select(tab.frame)

    def register_bot(self, bot: CryptoGamesBot, bottab: BotTab):
        with self.lock:
            init = safe_decimal(getattr(bot, "initial_bank", "0"))
            curr = init
            last = safe_decimal(getattr(bot, "last_successful_bank", init))
            self.active_bots[bot.bot_id] = bot
            self.bot_tabs[bot.bot_id] = bottab
            self.all_banks[bot.bot_id] = {"current_bank": curr, "initial_bank": init, "last_successful_bank": last}
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
                    last = safe_decimal(stats.get("last_successful_bank", init))
                    if init <= 0:
                        init = curr
                    with self.lock:
                        self.all_banks[bot_id] = {"current_bank": curr, "initial_bank": init, "last_successful_bank": last}
                    tab = self.bot_tabs.get(bot_id)
                    if tab:
                        tab.update_bank_ui(stats)
                    self._update_aggregate_label()
                except Exception:
                    pass

            processed += 1

        self._check_global_limits()
        self._check_global_recovery()
        self.root.after(self.ui_poll_ms, self._process_ui_queue)

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

    def _check_global_limits(self):
        if self.global_stop_fired is True:
            return

        tp_enabled = bool(self.global_tp_enabled.get())
        sl_enabled = bool(self.global_sl_enabled.get())
        if not tp_enabled and not sl_enabled:
            return

        total_initial, total_current = self._aggregate_initial_and_current()
        if total_initial <= 0:
            return

        growth_pct = (total_current - total_initial) * Decimal("100") / total_initial

        if tp_enabled:
            try:
                tp = Decimal(str(self.global_tp_percent_var.get()).strip())
            except Exception:
                tp = Decimal("0")
            if tp > 0 and growth_pct >= tp:
                self._trigger_global_stop(kind="TP", growth=growth_pct, limit=tp)
                return

        if sl_enabled:
            try:
                sl = Decimal(str(self.global_sl_percent_var.get()).strip())
            except Exception:
                sl = Decimal("0")
            if sl > 0 and growth_pct <= -sl:
                self._trigger_global_stop(kind="SL", growth=growth_pct, limit=sl)
                return

    def _check_global_recovery(self):
        with self.lock:
            active = list(self.active_bots.values())
            N = len(active)
            if N == 0:
                return
            shared_S_ref = Decimal("0")
            sum_current = Decimal("0")
            for bot in active:
                rec = self.all_banks.get(bot.bot_id, {})
                curr = safe_decimal(rec.get("current_bank"), "0")
                sref = safe_decimal(rec.get("last_successful_bank"), "0")
                sum_current += curr
                if sref > shared_S_ref:
                    shared_S_ref = sref

        if shared_S_ref <= 0:
            return

        denom = shared_S_ref * Decimal(N)
        deficit_abs = max(Decimal("0"), denom - sum_current)
        dd_pct = (deficit_abs * Decimal("100") / denom) if denom > 0 else Decimal("0")

        try:
            trig_pct = Decimal(str(self.recovery_dd_percent_var.get()).strip())
        except Exception:
            trig_pct = Decimal("0")
        if trig_pct <= 0:
            trig_pct = Decimal("0")

        try:
            trig_usdt = Decimal(str(self.recovery_dd_usdt_var.get()).strip())
        except Exception:
            trig_usdt = Decimal("0")
        if trig_usdt <= 0:
            trig_usdt = Decimal("0")

        trigger_by_pct = (trig_pct > 0 and dd_pct >= trig_pct)
        trigger_by_usdt = (trig_usdt > 0 and deficit_abs >= trig_usdt)

        if (not self.recovery_global_active) and (trigger_by_pct or trigger_by_usdt):
            self.recovery_global_active = True
            with self.lock:
                for bot in active:
                    try:
                        bot.enter_recovery(shared_S_ref, N)
                    except Exception:
                        pass
            print(f"[Manager] [RECOVERY] Global start: dd%={dd_pct:.2f}% (thr%={trig_pct}) deficit={deficit_abs:.8f} (thrUSDT={trig_usdt}) S_ref={shared_S_ref:.8f} bots={N}")
            return

        if self.recovery_global_active:
            any_in_recovery = False
            with self.lock:
                for bot in self.active_bots.values():
                    if getattr(bot, "recovery_active", False):
                        any_in_recovery = True
                        break
            if not any_in_recovery:
                self.recovery_global_active = False
                print("[Manager] [RECOVERY] Global completed: all bots back to normal")

    def force_end_recovery(self, initiator_id: Optional[str] = None):
        with self.lock:
            bots_seq = list(self.active_bots.values())
            for bot in bots_seq:
                try:
                    if getattr(bot, "recovery_active", False):
                        bot.recovery_active = False
                    bot.recovery_shared_S_ref = None
                    bot.recovery_target_end = None
                    bot.recovery_payout = Decimal(getattr(bot.config, "recovery_min_payout", 50))
                    if bot.strategy:
                        try:
                            bot.strategy.reset()
                        except Exception:
                            pass
                    # Сброс банка (avoid big bets)
                    try:
                        current_bal = bot.get_current_balance()
                    except Exception:
                        current_bal = Decimal("0")
                    if current_bal > 0:
                        bot.initial_bank = current_bal
                        bot.last_successful_bank = current_bal
                        bot.profit_global = Decimal("0")
                        self.enqueue(('bank', bot.bot_id, {
                            "initial_bank": bot.initial_bank,
                            "last_successful_bank": bot.last_successful_bank,
                            "current_bank": current_bal,
                            "profit_global": bot.profit_global,
                            "bot_id": bot.bot_id
                        }))
                    bot.paused = True
                    self.enqueue(('log', bot.bot_id, "[RECOVERY] ⏹ Force stop: global completion → reset base strategy; reset bank to current (avoid big bets); paused for staggered resume"))
                except Exception:
                    pass
            self.recovery_global_active = False

        print(f"[Manager] [RECOVERY] Force-completed by {initiator_id or 'unknown'}: all bots back to normal")

        with self.lock:
            bots_seq = list(self.active_bots.values())

        for idx, bot in enumerate(bots_seq):
            def resume_bot(b=bot):
                try:
                    b.paused = False
                    self.enqueue(('log', b.bot_id, "[Manager] Resume base strategy after recovery (staggered 5s)"))
                except Exception:
                    pass
            try:
                self.root.after(5000 * (idx + 1), resume_bot)
            except Exception:
                threading.Thread(target=lambda: (time.sleep(5 * (idx + 1)), resume_bot()), daemon=True).start()

    def _trigger_global_stop(self, kind: str, growth: Decimal, limit: Decimal):
        self.global_stop_fired = True
        msg = f"[Manager] Global {kind} triggered: growth={growth:.2f}% limit={limit:.2f}% → STOP ALL"
        print(msg)
        try:
            messagebox.showinfo("Global limit", msg)
        except Exception:
            pass
        self.stop_all_bots()

    def _update_aggregate_label(self):
        total_initial, total_current = self._aggregate_initial_and_current()
        total_profit = total_current - total_initial
        sign = "+" if total_profit >= 0 else ""
        col = "darkgreen" if total_profit >= 0 else "red"
        try:
            self.agg_label.config(text=f"Aggregate: Current={total_current:.8f} Profit={sign}{total_profit:.8f}", foreground=col)
        except:
            pass

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
        tabs_seq = list(self.bot_tabs.values())

        for idx, tab in enumerate(tabs_seq):
            def start_one(t=tab):
                try:
                    if not t.bot or not t.bot.is_running:
                        t.start_bot()
                except Exception as e:
                    tb = traceback.format_exc()
                    self.enqueue(('log', t.bot_name, f"Error starting: {e}"))
                    self.enqueue(('trace', t.bot_name, tb))
            try:
                self.root.after(5000 * (idx + 1), start_one)
            except Exception:
                threading.Thread(target=lambda: (time.sleep(5 * (idx + 1)), start_one()), daemon=True).start()

        self.enqueue(('log', 'Manager', "Start all requested (staggered 5s)"))

    def run(self):
        self.root.mainloop()

if __name__ == "__main__":
    app = BotManagerApp(ui_poll_ms=100)
    app.run()