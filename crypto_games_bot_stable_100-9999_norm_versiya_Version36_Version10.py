#!/usr/bin/env python3
# DuckDice multi-bot GUI — multithreaded UI queue
# Double-Press + Recovery + SIM RNG (casino-like) + Auto Recovery trigger by USDT drawdown to last successful bank
#
# Правки:
# A) Исправлен вывод логов в GUI (последние 200 строк, цвет win/loss, стабильный render)
# C) Добавлена подробная статистика расчёта ставки (mode=BASE/RECOVERY) перед каждым бетом
#
# Остальная логика не менялась.

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
import secrets

getcontext().prec = 40

API_BASE = "https://duckdice.io"
SIM_DEFAULT_INITIAL_BANK = Decimal("100.0")

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
MAX_API_CHANCE = Decimal("98.00")

# ------------------ API ------------------
class APIClient:
    def __init__(self, api_base: str = API_BASE, timeout: int = 15):
        self.base = api_base.rstrip("/")
        self.timeout = timeout
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": "DuckDiceBotAdapter/1.0",
            "Content-Type": "application/json",
            "Accept": "application/json",
        })

    def _get(self, path: str, params: Optional[dict] = None):
        url = f"{self.base}{path}"
        try:
            r = self.session.get(url, params=params, timeout=self.timeout)
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            try:
                return {"error": r.json()}
            except Exception:
                return {"error": str(e)}

    def _post(self, path: str, payload: dict, params: Optional[dict] = None):
        url = f"{self.base}{path}"
        try:
            r = self.session.post(url, params=params, json=payload, timeout=self.timeout)
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            try:
                return {"error": r.json()}
            except Exception:
                return {"error": str(e)}

    def bot_stats(self, coin: str, key: str):
        return self._get(f"/api/bot/stats/{coin}", params={"api_key": key})

    def bot_user_info(self, key: str):
        return self._get("/api/bot/user-info", params={"api_key": key})

    def placebet(self, coin: str, key: str, bet_amount, payout, underover_bool, client_seed):
        # Convert payout -> chance percent
        try:
            payout_d = Decimal(str(payout))
        except Exception:
            payout_d = Decimal("2")

        try:
            chance = (Decimal("100") / payout_d)
        except Exception:
            chance = Decimal("50")

        if chance < MIN_API_CHANCE:
            chance = MIN_API_CHANCE
        if chance > MAX_API_CHANCE:
            chance = MAX_API_CHANCE

        payload = {
            "symbol": str(coin),
            "amount": str(bet_amount),
            "chance": f"{chance:.2f}",
            "isHigh": True,   # always high
            "faucet": False
        }

        res = self._post("/api/dice/play", payload, params={"api_key": key})

        if isinstance(res, dict) and res.get("error"):
            return {"error": res.get("error")}
        if isinstance(res, dict) and res.get("errors"):
            return {"error": res.get("errors")}

        try:
            bet = res.get("bet", {}) if isinstance(res, dict) else {}
            user = res.get("user", {}) if isinstance(res, dict) else {}

            profit = safe_decimal(bet.get("profit", "0"))
            balance = safe_decimal(user.get("balance", "0"))

            num = bet.get("number", None)
            roll = None
            try:
                if num is not None:
                    roll = float(Decimal(int(num)) / Decimal("100"))
            except Exception:
                roll = None

            return {"Profit": float(profit), "Balance": float(balance), "Roll": roll}
        except Exception as e:
            return {"error": str(e)}

    def generate_client_seed(self) -> str:
        return ''.join(random.choice(string.ascii_letters + string.digits) for _ in range(16))

# ------------------ Utils ------------------
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

# ------------------ Strategy (сканирование payout) ------------------
class LinearPayoutStrategy:
    def __init__(self, start_payout=Decimal("100"), max_payout=Decimal("9999")):
        self.start_payout = Decimal(start_payout)
        self.max_payout = Decimal(max_payout)
        self.current_payout = Decimal(start_payout)

        self.circle_had_win = False
        self.target_pct = Decimal("0")  # 0..1

    def reset(self):
        self.current_payout = Decimal(self.start_payout)
        self.circle_had_win = False
        self.target_pct = Decimal("0")

    def on_spin_result(self, win: bool):
        if win:
            self.circle_had_win = True

    def on_wrap(self):
        if self.circle_had_win:
            self.target_pct = min(Decimal("1"), self.target_pct + Decimal("0.25"))
        else:
            if self.target_pct <= 0:
                self.target_pct = Decimal("1")
            else:
                self.target_pct = (self.target_pct / Decimal("2"))
        self.circle_had_win = False

    def next_payout_and_bet(self, state):
        payout = self.current_payout
        nxt = payout + Decimal(1)
        wrapped = False
        if nxt > self.max_payout:
            nxt = Decimal(self.start_payout)
            wrapped = True
        self.current_payout = nxt
        bet = Decimal(state.get("min_bet", Decimal("0.001"))) or Decimal("0.001")
        return payout, bet, 1, wrapped

# ------------------ Core Bot ------------------
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
        self._prev_payout = None
        self.manager_ref = None

        # Recovery (оставлено как было)
        self.recovery_enabled = False
        self.recovery_active = False
        self.recovery_pct_activation = Decimal("0")
        self.recovery_pct_total_losses = Decimal("0")
        self.recovery_trigger_threshold = Decimal("95.0")
        self.recovery_trigger_pct_bank = Decimal("0")
        self.recovery_activation_loss = Decimal("0")
        self.recovery_losses_so_far = Decimal("0")

        self.recovery_payout_min = Decimal("50")
        self.recovery_payout_max = Decimal("1000")
        self.recovery_payout_step = Decimal("2")
        self.recovery_direction_desc = True
        self.recovery_spin_stride = 1

        self.recovery_Ms = self._gen_recovery_Ms(
            desc=self.recovery_direction_desc,
            min_payout=self.recovery_payout_min,
            max_payout=self.recovery_payout_max,
            step=self.recovery_payout_step
        )
        self.recovery_i = 0
        self.recovery_last_roll = None
        self._pending_recovery_trigger = False
        self.recovery_auto_threshold_usdt = Decimal("0")

        self.recovery_bet_cap_pct_of_bank = Decimal("0.01")
        self.recovery_drawdown_intensity = Decimal("0.5")

        # SIM
        self.sim_mode = False
        self.sim_balance = Decimal("0")

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

    def _gen_recovery_Ms(self, desc=True, min_payout: Optional[Decimal]=None,
                         max_payout: Optional[Decimal]=None, step: Optional[Decimal]=None):
        try:
            mn = Decimal(min_payout) if min_payout is not None else Decimal("50")
            mx = Decimal(max_payout) if max_payout is not None else Decimal("1000")
            st = Decimal(step) if step is not None else Decimal("2")
        except Exception:
            mn, mx, st = Decimal("50"), Decimal("1000"), Decimal("2")

        if mn < Decimal("2"):
            mn = Decimal("2")
        if mx > Decimal("20000"):
            mx = Decimal("20000")
        if mx < mn:
            mn, mx = mx, mn
        try:
            st_abs = int(abs(int(st)))
        except Exception:
            st_abs = 1
        if st_abs <= 0:
            st_abs = 1

        Ms = []
        if desc:
            cur = mx
            while cur >= mn:
                Ms.append(Decimal(int(cur)))
                cur = cur - st_abs
        else:
            cur = mn
            while cur <= mx:
                Ms.append(Decimal(int(cur)))
                cur = cur + st_abs
        if not Ms:
            Ms = [Decimal("50")]
        return Ms

    def _recovery_min_bet_eff(self):
        eff = self.min_bet
        if eff <= 0:
            eff = Decimal("0.001")
        eff = max(eff, self.config.min_bet_enforced)
        return eff

    def _compute_recovery_bet(self, current_balance: Decimal,
                              payout: Decimal,
                              target_T: Decimal,
                              min_bet_eff: Decimal,
                              baseline_for_drawdown: Optional[Decimal] = None) -> Decimal:
        if current_balance <= 0:
            return min_bet_eff

        if payout <= 1:
            payout = Decimal(2)

        if baseline_for_drawdown is None:
            baseline_for_drawdown = self.last_successful_bank if self.last_successful_bank is not None else (self.initial_bank or current_balance)

        try:
            denom = baseline_for_drawdown if baseline_for_drawdown and baseline_for_drawdown > 0 else current_balance
            relative_dd = (baseline_for_drawdown - current_balance) / denom
            if relative_dd < 0:
                relative_dd = Decimal("0")
            if relative_dd > 1:
                relative_dd = Decimal("1")
        except Exception:
            relative_dd = Decimal("0")

        adj_T = target_T * (Decimal("1") + (self.recovery_drawdown_intensity * relative_dd))
        need = (adj_T / (payout - Decimal(1))) if adj_T > 0 else min_bet_eff

        cap_pct = self.recovery_bet_cap_pct_of_bank
        if cap_pct <= 0:
            cap_pct = Decimal("0.01")
        cap_abs = current_balance * cap_pct

        bet = min(need, cap_abs)
        bet = max(bet, min_bet_eff)
        bet = quantize_bet(bet)

        try:
            if bet > self.config.max_bet_limit:
                bet = Decimal(self.config.max_bet_limit)
        except Exception:
            pass

        if bet > current_balance:
            bet = quantize_bet(current_balance)

        return bet

    def _sim_roll_value(self) -> float:
        return secrets.randbelow(1000000) / 10000.0

    def _sim_win_for_M(self, M: int) -> bool:
        return secrets.randbelow(int(M)) == 0

    def _simulate_placebet(self, bet: Decimal, payout: Decimal):
        roll = self._sim_roll_value()
        win = self._sim_win_for_M(int(payout))
        if win:
            profit = bet * (payout - Decimal(1))
        else:
            profit = -bet
        self.sim_balance = (self.sim_balance + profit).quantize(Decimal("0.00000001"))
        return {"Profit": float(profit), "Balance": float(self.sim_balance), "Roll": roll}

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
        if self.sim_mode:
            self._push_bank_payload(self.sim_balance)
            return self.sim_balance
        if not self.config.api_key:
            return Decimal("0")

        try:
            res = self.api.bot_stats(self.config.coin, self.config.api_key)
            if isinstance(res, dict) and isinstance(res.get("balances"), dict):
                bal = safe_decimal(res["balances"].get("main", "0"))
                self._push_bank_payload(bal)
                return bal
        except Exception:
            pass
        return Decimal("0")

    def fetch_settings_if_needed(self):
        if self.sim_mode:
            self.min_bet = max(Decimal("0.001"), self.config.min_bet_enforced)
            return
        now = time.time()
        if now - self._last_min_bet_fetch < self.config.min_bet_refresh_secs:
            return
        self._last_min_bet_fetch = now
        self.min_bet = max(Decimal("0.001"), self.config.min_bet_enforced)

    def start(self):
        if not self.config.api_key:
            self.sim_mode = True
            if self.sim_balance <= 0:
                self.sim_balance = SIM_DEFAULT_INITIAL_BANK
            self._log(f"[{self.bot_id}] ▶ SIM mode (no API key). Start balance={self.sim_balance:.8f}")

        if not self.sim_mode and self.strategy is None:
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
            payout = None
            bet = None
            wrapped = False

            # --- compute bet ---
            if self.recovery_active:
                min_bet_eff = self._recovery_min_bet_eff()
                try:
                    M = self.recovery_Ms[self.recovery_i]
                except Exception:
                    self.recovery_i = 0
                    M = self.recovery_Ms[self.recovery_i]
                payout = Decimal(M)

                target_T = (self.recovery_pct_activation * self.recovery_activation_loss) + \
                           (self.recovery_pct_total_losses * self.recovery_losses_so_far)

                bet = self._compute_recovery_bet(current_balance, payout, target_T, min_bet_eff,
                                                 baseline_for_drawdown=self.last_successful_bank)
                mode = "RECOVERY"

                # C) calc log for RECOVERY
                try:
                    self._log(
                        f"[CALC] mode=RECOVERY payout={int(payout)} "
                        f"bal={current_balance:.8f} "
                        f"min_bet={min_bet_eff:.8f} "
                        f"target_T={target_T:.8f} bet={bet:.8f}"
                    )
                except Exception:
                    pass
            else:
                try:
                    payout, _, _, wrapped = self.strategy.next_payout_and_bet({"min_bet": self.min_bet})
                except Exception as e:
                    self._log(f"[{self.bot_id}] Strategy error: {e}")
                    time.sleep(1)
                    continue

                base_bet = Decimal(max(self.config.base_bet, self.config.min_bet_enforced))
                bet = base_bet

                baseline = self.last_successful_bank if self.last_successful_bank is not None else (self.initial_bank or current_balance)
                drawdown = baseline - current_balance
                if drawdown < 0:
                    drawdown = Decimal("0")

                target_pct = Decimal(getattr(self.strategy, "target_pct", Decimal("0")) or Decimal("0"))

                target_amount = Decimal("0")
                bet_req = Decimal("0")
                if (drawdown > 0) and (target_pct > 0) and (Decimal(payout) > 1):
                    target_amount = drawdown * target_pct
                    bet_req = target_amount / (Decimal(payout) - Decimal(1))
                    bet_req = quantize_bet(bet_req)

                    bet = max(base_bet, bet_req, self.config.min_bet_enforced)
                    if bet > self.config.max_bet_limit:
                        bet = Decimal(self.config.max_bet_limit)
                    bet = quantize_bet(bet)

                # C) calc log for BASE (include chance)
                try:
                    chance = Decimal("100") / Decimal(payout)
                    if chance < MIN_API_CHANCE:
                        chance = MIN_API_CHANCE
                    if chance > MAX_API_CHANCE:
                        chance = MAX_API_CHANCE
                    self._log(
                        f"[CALC] mode=BASE payout={int(payout)} chance={chance:.2f}% "
                        f"baseline={baseline:.8f} bal={current_balance:.8f} dd={drawdown:.8f} "
                        f"tpct={target_pct:.4f} target={target_amount:.8f} "
                        f"bet_req={bet_req:.8f} bet={bet:.8f}"
                    )
                except Exception:
                    pass

                if wrapped:
                    try:
                        self.strategy.on_wrap()
                    except Exception:
                        pass

            bet = quantize_bet(bet)
            if bet > current_balance:
                self._log(f"[{self.bot_id}] ❌ Недостаточно средств: balance={current_balance:.8f} bet={bet:.8f}")
                break

            client_seed = self.client_seed or (self.api.generate_client_seed() if not self.sim_mode else "SIM-SEED")

            if self.sim_mode:
                res = self._simulate_placebet(bet, payout)
            else:
                res = self.api.placebet(self.config.coin, self.config.api_key, str(bet), str(payout), True, client_seed)

            if not self.sim_mode and isinstance(res, dict) and res.get("error"):
                self._log(f"[{self.bot_id}] API error: {res.get('error')}")
                time.sleep(1)
                continue

            profit = safe_decimal(res.get("Profit", "0"))
            new_balance = safe_decimal(res.get("Balance", current_balance))
            roll_val = res.get("Roll", None)
            roll_str = f"{roll_val:.10f}" if isinstance(roll_val, float) else ("n/a" if roll_val is None else str(roll_val))
            win = profit > 0

            if mode == "BASE":
                try:
                    self.strategy.on_spin_result(bool(win))
                except Exception:
                    pass

            prefix = "[WIN]" if win else "[LOSS]"
            if mode == "RECOVERY":
                prefix = "[WIN-RECOVERY]" if win else "[LOSS-RECOVERY]"

            if win:
                self.stats["wins"] += 1
                self.stats["profit"] += profit
                self.stats["current_streak"] = max(0, self.stats["current_streak"] + 1)
                self.loss_sum = Decimal("0")
                self.streak = 0
                if self.last_successful_bank is None or new_balance > self.last_successful_bank:
                    self.last_successful_bank = new_balance
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

            self.spin_count += 1
            self.local_nonce += 1
            time.sleep(max(0.01, self.config.speed_ms / 1000.0))

        self._log(f"[{self.bot_id}] 🛑 Остановлен")

    def stop(self):
        self.is_running = False
        self.paused = False

# ------------------ UI Tab ------------------
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
        self.seed_entry = ttk.Entry(left, width=20)

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
        ttk.Label(left, text="Client Seed:").grid(row=10,column=0,sticky="w"); self.seed_entry.grid(row=10,column=1,padx=4)

        btnf = ttk.Frame(left); btnf.grid(row=15,column=0,columnspan=2,pady=(8,0))
        self.start_btn.pack(in_=btnf, side="left", padx=4)
        self.pause_btn.pack(in_=btnf, side="left", padx=4)
        self.stop_btn.pack(in_=btnf, side="left", padx=4)
        self.seed_btn.pack(in_=btnf, side="left", padx=4)

        bank_frame = ttk.LabelFrame(right, text="Bank", padding=6)
        bank_frame.pack(fill="x", pady=(0,6))
        self.initial_bank_lbl = ttk.Label(bank_frame, text="Initial: 0.00000000 USDT"); self.initial_bank_lbl.pack(anchor="w")
        self.last_bank_lbl = ttk.Label(bank_frame, text="Last successful: 0.00000000 USDT"); self.last_bank_lbl.pack(anchor="w")
        self.current_bank_lbl = ttk.Label(bank_frame, text="Current: 0.00000000 USDT"); self.current_bank_lbl.pack(anchor="w")

        ttk.Label(right, text=f"{self.bot_name} Last 200 logs").pack(anchor="w")
        self.log_text = scrolledtext.ScrolledText(right, height=22)
        self.log_text.pack(fill="both", expand=True)
        self.log_text.tag_config("win", foreground="green")
        self.log_text.tag_config("loss", foreground="red")

        # A) keep last N log lines and render reliably
        self._bet_lines = deque(maxlen=200)

        os.makedirs("logs", exist_ok=True)
        safe_name = self.bot_name.replace("/", "_").replace("\\", "_")
        self.log_file_path = os.path.join("logs", f"{safe_name}.txt")

        self.coin_box.set("USDT")
        self.bet_entry.insert(0, "0.001")
        self.enforced_min_entry.insert(0, "0.001")
        self.max_bet_entry.insert(0, "1.0")
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
            with open(self.log_file_path, "a", encoding="utf-8") as f:
                f.write(f"{ts} {msg}\n")
        except Exception as e:
            print(f"[{self.bot_name}] File log error: {e}")

    def _render_log(self):
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        for line, tag in self._bet_lines:
            self.log_text.insert("end", line + "\n", (tag,) if tag else ())
        self.log_text.see("end")
        self.log_text.configure(state="disabled")

    def log(self, msg: str):
        # A) decide coloring by message prefix
        tag = None
        low = msg.lower()
        if low.startswith("[win"):
            tag = "win"
        elif low.startswith("[loss"):
            tag = "loss"

        ts = time.strftime("%H:%M:%S")
        line = f"{ts} {msg}"

        # console
        print(f"{ts} [{self.bot_name}] {msg}")

        # file
        self._file_log(f"[{self.bot_name}] {msg}")

        # GUI
        self._bet_lines.append((line, tag))
        try:
            self.frame.after(0, self._render_log)
        except Exception:
            self._render_log()

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
        return cfg

    def start_bot(self):
        cfg = self.apply_settings_to_config()
        min_payout = self._parse_decimal(self.min_payout_entry.get(), "100")
        max_payout = self._parse_decimal(self.max_payout_entry.get(), "9999")

        api_client = APIClient()
        bot_id = f"{self.bot_name}"

        def log_cb(msg: str):
            self.manager.enqueue(('log', bot_id, msg))

        bank_cb = lambda stats: self.manager.enqueue(('bank', bot_id, stats))
        stats_cb = lambda stats: self.manager.enqueue(('stats', bot_id, stats))

        self.bot = CryptoGamesBot(bot_id, api_client, cfg, log_cb, bank_cb, stats_cb, executor=self.manager.executor)

        def linear_factory():
            return LinearPayoutStrategy(start_payout=min_payout, max_payout=max_payout)

        self.bot.set_strategy_factories([linear_factory])
        self.bot.set_strategy(linear_factory())

        seed = self.seed_entry.get().strip()
        if seed:
            self.bot.client_seed = seed

        self.start_btn.config(state="disabled")
        self.pause_btn.config(state="normal")
        self.stop_btn.config(state="normal")
        self.bot_thread = threading.Thread(target=self.bot.start, daemon=True)
        self.bot_thread.start()
        self.manager.register_bot(self.bot, self)

    def toggle_pause(self):
        if not self.bot:
            return
        paused = self.bot.pause_toggle()
        self.pause_btn.config(text="Resume" if paused else "Pause")
        self.manager.enqueue(('log', self.bot_name, "Paused" if paused else "Resumed"))

    def stop_bot(self):
        if self.bot:
            self.bot.stop()
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

# ------------------ Manager ------------------
class BotManagerApp:
    def __init__(self, ui_poll_ms: int = 100):
        self.root = tk.Tk()
        self.root.title("DuckDice Multi-Bot Manager")
        self.root.geometry("1200x840")
        self.bot_tabs = {}
        self.active_bots = {}
        self.all_banks = {}
        self.lock = threading.Lock()
        self.ui_queue = queue.Queue()
        max_workers = min(32, (os.cpu_count() or 4) * 5)
        self.executor = ThreadPoolExecutor(max_workers=max_workers)
        self.ui_poll_ms = ui_poll_ms

        self._build_ui()
        self.new_bot_tab()
        self.root.after(self.ui_poll_ms, self._process_ui_queue)

    def _build_ui(self):
        top = ttk.Frame(self.root); top.pack(fill="x", padx=6, pady=6)
        ttk.Button(top, text="New Bot", command=self.new_bot_tab).pack(side="left")
        ttk.Button(top, text="Start All", command=self.start_all_bots).pack(side="left", padx=6)
        ttk.Button(top, text="Stop All", command=self.stop_all_bots).pack(side="left", padx=6)
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
            self.active_bots[bot.bot_id] = bot
            self.bot_tabs[bot.bot_id] = bottab
            self.all_banks[bot.bot_id] = {"current_bank": curr, "initial_bank": init}

    def unregister_bot(self, bot_id: str):
        with self.lock:
            self.active_bots.pop(bot_id, None)
            self.all_banks.pop(bot_id, None)

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
                    tab = self.bot_tabs.get(bot_id)
                    if tab:
                        tab.update_bank_ui(stats)
                except Exception:
                    pass

            # 'stats' event ignored as in original minimal manager

            processed += 1

        self.root.after(self.ui_poll_ms, self._process_ui_queue)

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

    def run(self):
        self.root.mainloop()

# ------------------ Entry ------------------
if __name__ == "__main__":
    app = BotManagerApp(ui_poll_ms=100)
    app.run()