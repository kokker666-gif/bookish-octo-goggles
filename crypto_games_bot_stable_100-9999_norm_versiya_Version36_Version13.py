#!/usr/bin/env python3
# Crypto.Games multi-bot GUI — multithreaded UI queue
# Double-Press + Recovery + SIM RNG (casino-like) + Auto Recovery trigger by USDT drawdown to last successful bank
#
# Правки в этом коммите:
# - Добавлены расширенные настройки стратегии Recovery: конфиг payout (min/max/step, направление) и шаг спина (stride).
# Больше ничего не изменено.

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

API_BASE = "https://api.crypto.games/v1"
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
MAX_API_CHANCE = Decimal("9920")

# ------------------ API ------------------
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
    """
    Линейная стратегия сканирования payout: от min_payout до max_payout, +1 на каждый спин, на WRAP — сброс.
    """
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
        self.payout_wraps = 0
        self._prev_payout = None
        self.manager_ref = None

        # Double-Press
        self.press_active = False
        self.press_left = 0
        self.press_payout = None
        self.press_bet = Decimal("0.1")
        self.enable_highroll_99 = False

        # Recovery
        self.recovery_enabled = False
        self.recovery_active = False
        self.recovery_pct_activation = Decimal("0")
        self.recovery_pct_total_losses = Decimal("0")
        self.recovery_trigger_threshold = Decimal("95.0")
        self.recovery_trigger_pct_bank = Decimal("0")
        self.recovery_activation_loss = Decimal("0")
        self.recovery_losses_so_far = Decimal("0")

        # Расширенные настройки Recovery payout-сканирования и шага спина
        self.recovery_payout_min = Decimal("50")     # мин. payout в Recovery
        self.recovery_payout_max = Decimal("1000")   # макс. payout в Recovery
        self.recovery_payout_step = Decimal("2")     # шаг payout между спинами
        self.recovery_direction_desc = True          # направление: убывающее max→min
        self.recovery_spin_stride = 1                # сколько элементов списка Ms пропускать за один спин

        self.recovery_Ms = self._gen_recovery_Ms(
            desc=self.recovery_direction_desc,
            min_payout=self.recovery_payout_min,
            max_payout=self.recovery_payout_max,
            step=self.recovery_payout_step
        )
        self.recovery_i = 0
        self.recovery_last_roll = None
        self._pending_recovery_trigger = False
        # Auto recovery start threshold (USDT drawdown from baseline)
        self.recovery_auto_threshold_usdt = Decimal("0")

        # Лимитер ставки от текущего банка и интенсивность адаптации
        self.recovery_bet_cap_pct_of_bank = Decimal("0.01")  # максимум 1% от текущего банка
        self.recovery_drawdown_intensity = Decimal("0.5")    # 0..1 — сила влияния относительного drawdown

        # SIM mode
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

    # Recovery helpers
    def _gen_recovery_Ms(self, desc=True, min_payout: Optional[Decimal]=None,
                         max_payout: Optional[Decimal]=None, step: Optional[Decimal]=None):
        """
        Сгенерировать список Ms (payout) для Recovery по настройкам:
        - min_payout, max_payout (включительно)
        - step (шаг между значениями payout)
        - desc: направление (True — убывание max→min, False — возрастание min→max)
        """
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
        """
        Sizing recovery-ставки и логирование параметров:
        - relative_dd, adj_T, need, cap_abs и финальный bet будут залогированы.
        """
        if current_balance <= 0:
            bet = min_bet_eff
            # Лог при нулевом/отрицательном балансе
            self._log(f"[{self.bot_id}] [RECOVERY-CALC] balance<=0 → bet={bet:.8f}")
            return bet

        if payout <= 1:
            payout = Decimal(2)

        if baseline_for_drawdown is None:
            baseline_for_drawdown = self.last_successful_bank if self.last_successful_bank is not None else (self.initial_bank or current_balance)

        # relative drawdown
        try:
            denom = baseline_for_drawdown if baseline_for_drawdown and baseline_for_drawdown > 0 else current_balance
            relative_dd = (baseline_for_drawdown - current_balance) / denom
            if relative_dd < 0:
                relative_dd = Decimal("0")
            if relative_dd > 1:
                relative_dd = Decimal("1")
        except Exception:
            relative_dd = Decimal("0")

        # адаптация цели
        adj_T = target_T * (Decimal("1") + (self.recovery_drawdown_intensity * relative_dd))

        # базовая потребность ставки
        need = (adj_T / (payout - Decimal(1))) if adj_T > 0 else min_bet_eff

        # жёсткий кап от текущего банка
        cap_pct = self.recovery_bet_cap_pct_of_bank
        if cap_pct <= 0:
            cap_pct = Decimal("0.01")
        cap_abs = current_balance * cap_pct

        # итоговая ставка
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

        # Подробный лог расчёта
        try:
            self._log(f"[{self.bot_id}] [RECOVERY-CALC] payout={int(payout)} baseline={baseline_for_drawdown:.8f} "
                      f"current={current_balance:.8f} relative_dd={relative_dd:.6f} "
                      f"target_T={target_T:.8f} adj_T={adj_T:.8f} need={need:.8f} "
                      f"cap_pct={cap_pct:.4f} cap_abs={cap_abs:.8f} bet={bet:.8f}")
        except Exception:
            self._log(f"[{self.bot_id}] [RECOVERY-CALC] payout={payout} baseline={baseline_for_drawdown} "
                      f"current={current_balance} relative_dd={relative_dd} "
                      f"target_T={target_T} adj_T={adj_T} need={need} "
                      f"cap_pct={cap_pct} cap_abs={cap_abs} bet={bet}")

        return bet

    def start_recovery(self, pct_activation: Decimal, pct_total_losses: Decimal,
                       trigger_threshold: Decimal, trigger_pct_bank: Decimal):
        self.recovery_enabled = True
        current_balance = self.get_current_balance()
        init = self.initial_bank if self.initial_bank is not None else current_balance
        activation_loss = init - current_balance
        if activation_loss < 0:
            activation_loss = Decimal("0")
        self.recovery_activation_loss = activation_loss
        self.recovery_losses_so_far = Decimal("0")
        self.recovery_pct_activation = Decimal(pct_activation)
        self.recovery_pct_total_losses = Decimal(pct_total_losses)
        self.recovery_trigger_threshold = Decimal(trigger_threshold)
        self.recovery_trigger_pct_bank = Decimal(trigger_pct_bank)

        # Перегенерируем Ms на случай изменения конфигурации
        self.recovery_Ms = self._gen_recovery_Ms(
            desc=self.recovery_direction_desc,
            min_payout=self.recovery_payout_min,
            max_payout=self.recovery_payout_max,
            step=self.recovery_payout_step
        )
        self.recovery_i = 0

        self.recovery_last_roll = None
        self._pending_recovery_trigger = False
        self.recovery_active = True
        self._log(f"[{self.bot_id}] ▶ Recovery ON: act_loss={self.recovery_activation_loss:.8f} "
                  f"pct_act={self.recovery_pct_activation:.3f} pct_total={self.recovery_pct_total_losses:.3f} "
                  f"trg_thr={self.recovery_trigger_threshold} trg_pct_bank={self.recovery_trigger_pct_bank:.3f}")

    def _stop_recovery_for_all(self, triggering_balance: Decimal):
        try:
            mgr = self.manager_ref
            if mgr is None:
                return
            global_max = triggering_balance
            for bot in list(mgr.active_bots.values()):
                val = bot.last_successful_bank if bot.last_successful_bank is not None else bot.initial_bank
                if val is not None and val > global_max:
                    global_max = val
            for bot in list(mgr.active_bots.values()):
                bot.last_successful_bank = global_max
                bot.recovery_active = False
                bot._pending_recovery_trigger = False
                bot.recovery_losses_so_far = Decimal("0")
                bot.profit_global = Decimal("0")
                bot._log(f"[{bot.bot_id}] ▶ Recovery OFF (global sync), set last_successful={global_max:.8f}, profit reset (recovery_enabled=True)")
        except Exception:
            pass

    def stop_recovery(self, reason: str = ""):
        self.recovery_active = False
        self._pending_recovery_trigger = False
        if reason:
            self._log(f"[{self.bot_id}] ▶ Recovery OFF ({reason})")
        else:
            self._log(f"[{self.bot_id}] ▶ Recovery OFF")

    # SIM helpers
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

    # Logging & stats
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

    # API data
    def get_current_balance(self):
        if self.sim_mode:
            self._push_bank_payload(self.sim_balance)
            return self.sim_balance
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
        if self.sim_mode:
            self.min_bet = max(Decimal("0.001"), self.config.min_bet_enforced)
            return
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

    def _activate_press(self, payout: Decimal, reason: str):
        self.press_active = True
        self.press_left = 2
        self.press_payout = Decimal(payout)
        self._log(f"[{self.bot_id}] ▶ Press start: payout={int(self.press_payout)} bet={self.press_bet:.6f} (2 spins) reason={reason}")

    # Main loop
    def start(self):
        if not self.config.api_key:
            self.sim_mode = True
            if self.sim_balance <= 0:
                self.sim_balance = SIM_DEFAULT_INITIAL_BANK
            self._log(f"[{self.bot_id}] ▶ SIM mode (no API key). Start balance={self.sim_balance:.8f}")

        if not self.sim_mode and self.strategy is None:
            self._log(f"[{self.bot_id}] Нет стратегии.")
            return
        if not self.sim_mode and not self.config.api_key:
            self._log(f"[{self.bot_id}] Нет API ключа.")
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

            # Авто-старт Recovery от локального last_successful_bank
            try:
                if (not self.recovery_active) and bool(self.recovery_enabled) and (self.recovery_auto_threshold_usdt > 0):
                    baseline = (self.last_successful_bank if self.last_successful_bank is not None else (self.initial_bank or Decimal("0")))
                    if baseline > 0 and current_balance <= (baseline - self.recovery_auto_threshold_usdt):
                        self.start_recovery(self.recovery_pct_activation,
                                            self.recovery_pct_total_losses,
                                            self.recovery_trigger_threshold,
                                            self.recovery_trigger_pct_bank)
            except Exception:
                pass

            mode = "BASE"
            payout = None
            bet = None

            # 1) Основной бет: либо RECOVERY, либо BASE
            if self.recovery_active:
                if self.initial_bank is not None:
                    dyn_act_loss = (self.initial_bank - current_balance)
                    if dyn_act_loss < 0:
                        dyn_act_loss = Decimal("0")
                    self.recovery_activation_loss = dyn_act_loss

                trigger_now = False
                if self.recovery_last_roll is not None:
                    try:
                        if Decimal(self.recovery_last_roll) >= self.recovery_trigger_threshold:
                            trigger_now = True
                    except Exception:
                        trigger_now = False

                min_bet_eff = self._recovery_min_bet_eff()
                if trigger_now and self.recovery_trigger_pct_bank > 0:
                    payout = Decimal(5)
                    target_T = self.recovery_trigger_pct_bank * (current_balance if current_balance > 0 else (self.initial_bank or Decimal("0")))
                    bet = self._compute_recovery_bet(current_balance, payout, target_T, min_bet_eff,
                                                     baseline_for_drawdown=self.last_successful_bank)
                    mode = "RECOVERY-TRIGGER"
                    self.recovery_last_roll = Decimal("0")
                else:
                    try:
                        M = self.recovery_Ms[self.recovery_i]
                    except Exception:
                        self.recovery_Ms = self._gen_recovery_Ms(
                            desc=self.recovery_direction_desc,
                            min_payout=self.recovery_payout_min,
                            max_payout=self.recovery_payout_max,
                            step=self.recovery_payout_step
                        )
                        self.recovery_i = 0
                        M = self.recovery_Ms[self.recovery_i]
                    payout = Decimal(M)
                    target_T = (self.recovery_pct_activation * self.recovery_activation_loss) + \
                               (self.recovery_pct_total_losses * self.recovery_losses_so_far)
                    bet = self._compute_recovery_bet(current_balance, payout, target_T, min_bet_eff,
                                                     baseline_for_drawdown=self.last_successful_bank)
                    mode = "RECOVERY"

                if bet > current_balance:
                    if current_balance >= min_bet_eff:
                        bet = quantize_bet(current_balance)
                    else:
                        self._log(f"[{self.bot_id}] ❌ Недостаточно средств для recovery: balance={current_balance:.8f} min_bet={min_bet_eff:.8f}")
                        self.stop()
                        break

            else:
                if self.strategy is None:
                    self._log(f"[{self.bot_id}] Нет стратегии.")
                    break
                try:
                    payout, _, _, _ = self.strategy.next_payout_and_bet({"min_bet": self.min_bet})
                except Exception as e:
                    self._log(f"[{self.bot_id}] Strategy error: {e}")
                    time.sleep(1)
                    continue
                bet = Decimal(max(self.config.base_bet, self.config.min_bet_enforced))
                mode = "BASE"

            if mode not in ("RECOVERY", "RECOVERY-TRIGGER"):
                if self.strategy and hasattr(self.strategy, "max_payout"):
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

            client_seed = self.client_seed or (self.api.generate_client_seed() if not self.sim_mode else "SIM-SEED")

            # Выполняем основной бет
            if self.sim_mode:
                res = self._simulate_placebet(bet, payout)
            else:
                res = self.api.placebet(self.config.coin, self.config.api_key,
                                        float(bet), float(payout), True, client_seed)

            if not self.sim_mode and isinstance(res, dict) and res.get("error"):
                self._log(f"[{self.bot_id}] API error: {res.get('error')}")
                time.sleep(1)
                continue

            profit = safe_decimal(res.get("Profit", "0"))
            new_balance = safe_decimal(res.get("Balance", current_balance))
            roll_val = res.get("Roll", None)
            try:
                self.recovery_last_roll = Decimal(str(roll_val)) if (roll_val is not None) else None
            except Exception:
                self.recovery_last_roll = None

            roll_str = f"{roll_val:.10f}" if isinstance(roll_val, float) else ("n/a" if roll_val is None else str(roll_val))
            win = profit > 0

            if mode == "RECOVERY" or mode == "RECOVERY-TRIGGER":
                prefix = "[WIN-RECOVERY]" if win else "[LOSS-RECOVERY]"
            else:
                prefix = "[WIN]" if win else "[LOSS]"

            if win:
                self.stats["wins"] += 1
                self.stats["profit"] += profit
                self.stats["current_streak"] = max(0, self.stats["current_streak"] + 1)
                self.loss_sum = Decimal("0")
                self.streak = 0
                if self.last_successful_bank is None or new_balance > self.last_successful_bank:
                    self.last_successful_bank = new_balance

                if self.recovery_active and new_balance >= (self.last_successful_bank or new_balance):
                    self._stop_recovery_for_all(triggering_balance=new_balance)
                else:
                    try:
                        mgr = self.manager_ref
                        if mgr is not None:
                            global_max = new_balance
                            for bot in list(mgr.active_bots.values()):
                                val = bot.last_successful_bank if bot.last_successful_bank is not None else bot.initial_bank
                                if val is not None and val > global_max:
                                    global_max = val
                            for bot in list(mgr.active_bots.values()):
                                bot.last_successful_bank = global_max
                    except Exception:
                        pass

                if self.stop_on_win and (mode not in ("RECOVERY", "RECOVERY-TRIGGER")):
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

            # Обработка recovery
            if self.recovery_active:
                if win:
                    if self.initial_bank is not None:
                        dyn_act_loss_after_win = (self.initial_bank - new_balance)
                        if dyn_act_loss_after_win < 0:
                            dyn_act_loss_after_win = Decimal("0")
                        self.recovery_activation_loss = dyn_act_loss_after_win
                    if self.last_successful_bank is not None and new_balance >= self.last_successful_bank:
                        self._stop_recovery_for_all(triggering_balance=new_balance)
                else:
                    self.recovery_losses_so_far += bet
                    if mode == "RECOVERY":
                        # Учитываем шаг спина (stride)
                        stride = 1
                        try:
                            stride = int(self.recovery_spin_stride)
                        except Exception:
                            stride = 1
                        if stride <= 0:
                            stride = 1
                        self.recovery_i += stride
                        if self.recovery_i >= len(self.recovery_Ms):
                            self.recovery_direction_desc = not self.recovery_direction_desc
                            self.recovery_Ms = self._gen_recovery_Ms(
                                desc=self.recovery_direction_desc,
                                min_payout=self.recovery_payout_min,
                                max_payout=self.recovery_payout_max,
                                step=self.recovery_payout_step
                            )
                            self.recovery_i = 0
                            self._log(f"[{self.bot_id}] [RECOVERY] reverse direction (desc={self.recovery_direction_desc})")

            # PRESS-бет (как было)
            if self.press_active and self.press_left > 0 and self.press_payout is not None:
                press_payout = Decimal(self.press_payout)
                press_bet = Decimal(self.press_bet)
                press_bet = quantize_bet(press_bet)
                if press_bet > self.config.max_bet_limit:
                    press_bet = Decimal(self.config.max_bet_limit)
                try:
                    _ = Decimal("100") / press_payout
                except Exception:
                    pass

                if press_bet <= new_balance:
                    if self.sim_mode:
                        res2 = self._simulate_placebet(press_bet, press_payout)
                    else:
                        res2 = self.api.placebet(self.config.coin, self.config.api_key,
                                                 float(press_bet), float(press_payout), True, client_seed)
                    if not self.sim_mode and isinstance(res2, dict) and res2.get("error"):
                        self._log(f"[{self.bot_id}] API error (press): {res2.get('error')}")
                    else:
                        profit2 = safe_decimal(res2.get("Profit", "0"))
                        new_balance2 = safe_decimal(res2.get("Balance", new_balance))
                        roll2 = res2.get("Roll", None)
                        roll2_str = f"{roll2:.10f}" if isinstance(roll2, float) else ("n/a" if roll2 is None else str(roll2))
                        win2 = profit2 > 0

                        pref2 = "[WIN-PRESS]" if win2 else "[LOSS-PRESS]"
                        self._log(f"{pref2} spin {self.spin_count + 1} payout={int(press_payout)} roll={roll2_str} bet={press_bet:.8f} profit={profit2:.8f}" if win2 else f"{pref2} spin {self.spin_count + 1} payout={int(press_payout)} roll={roll2_str} bet={press_bet:.8f}")

                        if win2:
                            self.stats["wins"] += 1
                            self.stats["profit"] += profit2
                            self.stats["current_streak"] = max(0, self.stats["current_streak"] + 1)
                            try:
                                mgr = self.manager_ref
                                if mgr is not None:
                                    global_max = new_balance2
                                    for bot in list(mgr.active_bots.values()):
                                        val = bot.last_successful_bank if bot.last_successful_bank is not None else bot.initial_bank
                                        if val is not None and val > global_max:
                                            global_max = val
                                    for bot in list(mgr.active_bots.values()):
                                        bot.last_successful_bank = global_max
                                    if self.recovery_active and self.last_successful_bank is not None and new_balance2 >= self.last_successful_bank:
                                        self._stop_recovery_for_all(triggering_balance=new_balance2)
                            except Exception:
                                pass
                        else:
                            self.stats["losses"] += 1
                            self.stats["current_streak"] = min(0, self.stats["current_streak"] - 1)
                            self.loss_sum += press_bet
                            if self.loss_sum > self.stats["max_loss_sum"]:
                                self.stats["max_loss_sum"] = self.loss_sum
                            if press_bet > self.stats["max_bet"]:
                                self.stats["max_bet"] = press_bet

                        self.stats["total_bets"] += 1
                        self.stats["total_wagered"] += press_bet
                        self.profit_global = new_balance2 - (self.initial_bank if self.initial_bank is not None else Decimal("0"))
                        self._stats()
                        self._bank(new_balance2)
                        new_balance = new_balance2

                        if win2:
                            self.press_active = False
                            self.press_left = 0
                            self.press_payout = None
                        else:
                            self.press_left -= 1
                            if self.press_left <= 0:
                                self.press_active = False
                                self.press_payout = None
                else:
                    self._log(f"[{self.bot_id}] ⚠️ Недостаточно средств для press: balance={new_balance:.8f} press_bet={press_bet:.8f}")

            # Триггеры включения press (как было)
            if not self.paused:
                if self.enable_highroll_99 and (roll_val is not None):
                    try:
                        if Decimal(str(roll_val)) >= Decimal("99.000"):
                            self._activate_press(Decimal("100"), reason="highroll99")
                        else:
                            if Decimal("5") <= Decimal(payout) <= Decimal("8") and Decimal(str(roll_val)) >= Decimal("90.000"):
                                self._activate_press(Decimal("10"), reason="win-5-8-roll>=90" if win else "cond-5-8-roll>=90")
                    except Exception:
                        pass
                else:
                    try:
                        if Decimal("5") <= Decimal(payout) <= Decimal("8") and (roll_val is not None) and Decimal(str(roll_val)) >= Decimal("90.000"):
                            self._activate_press(Decimal("10"), reason="win-5-8-roll>=90" if win else "cond-5-8-roll>=90")
                    except Exception:
                        pass

            if self.recovery_active and (self.last_successful_bank is not None) and (new_balance >= self.last_successful_bank):
                self._stop_recovery_for_all(triggering_balance=new_balance)

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

        ttk.Checkbutton(left, text="Pause on FAIL", variable=self.pause_on_fail_var,
                        command=self._on_pause_on_fail_toggled).grid(row=10,column=0,columnspan=2,sticky="w")
        ttk.Checkbutton(left, text="Stop on WIN", variable=self.stop_on_win_var,
                        command=self._on_stop_on_win_toggled).grid(row=11,column=0,columnspan=2,sticky="w")

        ttk.Checkbutton(left, text="Enable HighRoll 99→payout 100 (2x @0.1)",
                        variable=self.enable_highroll_var).grid(row=12,column=0,columnspan=2,sticky="w",pady=(6,0))

        ttk.Label(left, text="Client Seed:").grid(row=13,column=0,sticky="w"); self.seed_entry.grid(row=13,column=1,padx=4)

        # Recovery UI
        recf = ttk.LabelFrame(left, text="Recovery", padding=6)
        recf.grid(row=14, column=0, columnspan=2, sticky="we", pady=(8,0))
        self.recovery_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(recf, text="Enable Recovery", variable=self.recovery_enabled_var,
                        command=self._on_recovery_toggled).grid(row=0, column=0, columnspan=2, sticky="w")

        ttk.Label(recf, text="Recover % of activation loss:").grid(row=1, column=0, sticky="w")
        self.rec_pct_activation_entry = ttk.Entry(recf, width=8); self.rec_pct_activation_entry.grid(row=1, column=1, sticky="e")
        self.rec_pct_activation_entry.insert(0, "50")

        ttk.Label(recf, text="Recover % of rec.losses:").grid(row=2, column=0, sticky="w")
        self.rec_pct_total_entry = ttk.Entry(recf, width=8); self.rec_pct_total_entry.grid(row=2, column=1, sticky="e")
        self.rec_pct_total_entry.insert(0, "50")

        ttk.Label(recf, text="Trigger roll ≥").grid(row=3, column=0, sticky="w")
        self.rec_trigger_thr_entry = ttk.Entry(recf, width=8); self.rec_trigger_thr_entry.grid(row=3, column=1, sticky="e")
        self.rec_trigger_thr_entry.insert(0, "95.000")

        ttk.Label(recf, text="Trigger: % of initial bank:").grid(row=4, column=0, sticky="w")
        self.rec_trigger_pct_entry = ttk.Entry(recf, width=8); self.rec_trigger_pct_entry.grid(row=4, column=1, sticky="e")
        self.rec_trigger_pct_entry.insert(0, "5")

        ttk.Label(recf, text="Auto start if drawdown ≥ (USDT):").grid(row=5, column=0, sticky="w")
        self.rec_auto_threshold_entry = ttk.Entry(recf, width=8); self.rec_auto_threshold_entry.grid(row=5, column=1, sticky="e")
        self.rec_auto_threshold_entry.insert(0, "0")

        ttk.Label(recf, text="Bet cap (% of current bank):").grid(row=6, column=0, sticky="w")
        self.rec_cap_pct_entry = ttk.Entry(recf, width=8); self.rec_cap_pct_entry.grid(row=6, column=1, sticky="e")
        self.rec_cap_pct_entry.insert(0, "1")  # 1%

        ttk.Label(recf, text="Drawdown intensity (0..1):").grid(row=7, column=0, sticky="w")
        self.rec_dd_intensity_entry = ttk.Entry(recf, width=8); self.rec_dd_intensity_entry.grid(row=7, column=1, sticky="e")
        self.rec_dd_intensity_entry.insert(0, "0.5")

        # Расширенные настройки стратегии Recovery
        ttk.Label(recf, text="Recovery payout min:").grid(row=8, column=0, sticky="w")
        self.rec_pay_min_entry = ttk.Entry(recf, width=8); self.rec_pay_min_entry.grid(row=8, column=1, sticky="e")
        self.rec_pay_min_entry.insert(0, "50")

        ttk.Label(recf, text="Recovery payout max:").grid(row=9, column=0, sticky="w")
        self.rec_pay_max_entry = ttk.Entry(recf, width=8); self.rec_pay_max_entry.grid(row=9, column=1, sticky="e")
        self.rec_pay_max_entry.insert(0, "1000")

        ttk.Label(recf, text="Payout step:").grid(row=10, column=0, sticky="w")
        self.rec_pay_step_entry = ttk.Entry(recf, width=8); self.rec_pay_step_entry.grid(row=10, column=1, sticky="e")
        self.rec_pay_step_entry.insert(0, "2")

        self.rec_desc_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(recf, text="Descending (max→min)", variable=self.rec_desc_var).grid(row=11, column=0, columnspan=2, sticky="w")

        ttk.Label(recf, text="Spin stride (indices per spin):").grid(row=12, column=0, sticky="w")
        self.rec_stride_entry = ttk.Entry(recf, width=8); self.rec_stride_entry.grid(row=12, column=1, sticky="e")
        self.rec_stride_entry.insert(0, "1")

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
        return cfg

    def start_bot(self):
        try:
            cfg = self.apply_settings_to_config()
        except Exception as e:
            self.manager.enqueue(('log', self.bot_name, f"Ошибка настроек: {e}"))
            self.manager.enqueue(('trace', self.bot_name, traceback.format_exc()))
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

            # Recovery parameters и авто-порог
            if bool(self.recovery_enabled_var.get()):
                self._apply_recovery_to_bot()
                try:
                    auto_thr = self._parse_decimal(self.rec_auto_threshold_entry.get(), "0")
                    if auto_thr < 0:
                        auto_thr = Decimal("0")
                    self.bot.recovery_auto_threshold_usdt = auto_thr
                    self.bot.recovery_enabled = True
                    self.manager.enqueue(('log', bot_id, f"Recovery auto threshold set: {auto_thr:.8f} USDT"))
                except Exception as e:
                    self.manager.enqueue(('log', bot_id, f"Recovery auto threshold error: {e}"))

            # SIM mode if no API key
            if not cfg.api_key:
                self.bot.sim_mode = True
                self.bot.sim_balance = SIM_DEFAULT_INITIAL_BANK
                self.manager.enqueue(('log', bot_id, f"SIM mode ON (no API key). Start balance={self.bot.sim_balance:.8f}"))

            self.start_btn.config(state="disabled")
            self.pause_btn.config(state="normal")
            self.stop_btn.config(state="normal")
            self.bot_thread = threading.Thread(target=self.bot.start, daemon=True)
            self.bot_thread.start()
            self.manager.register_bot(self.bot, self)
            self.manager.enqueue(('log', bot_id,
                                  f"Запущен payout {int(min_payout)}..{int(max_payout)} highroll99={self.bot.enable_highroll_99}"))
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

    def _apply_recovery_to_bot(self):
        if not self.bot:
            return
        try:
            pct_act = self._parse_decimal(self.rec_pct_activation_entry.get(), "50") / Decimal("100")
            pct_total = self._parse_decimal(self.rec_pct_total_entry.get(), "50") / Decimal("100")
            trg_thr = self._parse_decimal(self.rec_trigger_thr_entry.get(), "95.0")
            trg_pct = self._parse_decimal(self.rec_trigger_pct_entry.get(), "5") / Decimal("100")

            cap_pct_ui = self._parse_decimal(self.rec_cap_pct_entry.get(), "1")  # %
            dd_intensity_ui = self._parse_decimal(self.rec_dd_intensity_entry.get(), "0.5")

            # Новые Recovery настройки
            pay_min = self._parse_decimal(self.rec_pay_min_entry.get(), "50")
            pay_max = self._parse_decimal(self.rec_pay_max_entry.get(), "1000")
            pay_step = self._parse_decimal(self.rec_pay_step_entry.get(), "2")
            desc = bool(self.rec_desc_var.get())
            stride = self._parse_int(self.rec_stride_entry.get(), 1)

            if pct_act < 0: pct_act = Decimal("0")
            if pct_total < 0: pct_total = Decimal("0")
            if trg_pct < 0: trg_pct = Decimal("0")
            if cap_pct_ui < 0: cap_pct_ui = Decimal("0")
            if dd_intensity_ui < 0: dd_intensity_ui = Decimal("0")
            if dd_intensity_ui > 1: dd_intensity_ui = Decimal("1")

            if pay_min < Decimal("2"): pay_min = Decimal("2")
            if pay_max > Decimal("20000"): pay_max = Decimal("20000")
            if pay_max < pay_min: pay_min, pay_max = pay_max, pay_min
            try:
                if int(abs(int(pay_step))) <= 0:
                    pay_step = Decimal("1")
            except Exception:
                pay_step = Decimal("1")
            if stride <= 0: stride = 1

            self.bot.recovery_pct_activation = pct_act
            self.bot.recovery_pct_total_losses = pct_total
            self.bot.recovery_trigger_threshold = trg_thr
            self.bot.recovery_trigger_pct_bank = trg_pct

            self.bot.recovery_bet_cap_pct_of_bank = (cap_pct_ui / Decimal("100"))  # проценты → доля
            self.bot.recovery_drawdown_intensity = dd_intensity_ui

            # Применить payout-сканирование и шаг спина
            self.bot.recovery_payout_min = pay_min
            self.bot.recovery_payout_max = pay_max
            self.bot.recovery_payout_step = pay_step
            self.bot.recovery_direction_desc = desc
            self.bot.recovery_spin_stride = stride
            self.bot.recovery_Ms = self.bot._gen_recovery_Ms(
                desc=desc,
                min_payout=pay_min,
                max_payout=pay_max,
                step=pay_step
            )
            self.bot.recovery_i = 0

            self.bot.recovery_enabled = True
            self.manager.enqueue(('log', self.bot_name,
                                  f"Recovery parameters set (pct_act={pct_act:.3f}, pct_total={pct_total:.3f}, "
                                  f"trg_thr={trg_thr}, trg_pct_bank={trg_pct:.3f}, cap={cap_pct_ui:.3f}%, "
                                  f"dd_intensity={dd_intensity_ui:.3f})"))
        except Exception as e:
            self.manager.enqueue(('log', self.bot_name, f"Recovery setup error: {e}"))

    def _on_recovery_toggled(self):
        enabled = bool(self.recovery_enabled_var.get())
        if not self.bot:
            return
        if enabled:
            self._apply_recovery_to_bot()
            try:
                auto_thr = self._parse_decimal(self.rec_auto_threshold_entry.get(), "0")
                if auto_thr < 0:
                    auto_thr = Decimal("0")
                self.bot.recovery_auto_threshold_usdt = auto_thr
                self.bot.recovery_enabled = True
                self.manager.enqueue(('log', self.bot_name, f"Recovery auto threshold set: {auto_thr:.8f} USDT"))
            except Exception as e:
                self.manager.enqueue(('log', self.bot_name, f"Recovery auto threshold error: {e}"))
        else:
            try:
                self.bot.stop_recovery("manual")
            except Exception:
                pass

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
        self.root.title("Crypto.Games Multi-Bot Manager (Double-Press + Recovery + SIM RNG)")
        self.root.geometry("1200x840")
        self.bot_tabs = {}
        self.active_bots = {}
        self.all_banks = {}
        self.lock = threading.Lock()
        self.ui_queue = queue.Queue()
        max_workers = min(32, (os.cpu_count() or 4) * 5)
        self.executor = ThreadPoolExecutor(max_workers=max_workers)
        self.ui_poll_ms = ui_poll_ms

        # Global TP/SL
        self.global_tp_enabled = tk.BooleanVar(value=False)
        self.global_sl_enabled = tk.BooleanVar(value=False)
        self.global_tp_percent_var = tk.StringVar(value="10")
        self.global_sl_percent_var = tk.StringVar(value="10")
        self.global_stop_fired = False

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
                    if init <= 0:
                        init = curr
                    with self.lock:
                        self.all_banks[bot_id] = {"current_bank": curr, "initial_bank": init}
                    tab = self.bot_tabs.get(bot_id)
                    if tab:
                        tab.update_bank_ui(stats)
                    self._update_aggregate_label()
                except Exception:
                    pass

            processed += 1

        self._check_global_limits()
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

    def _parse_percent(self, s: str) -> Optional[Decimal]:
        try:
            p = Decimal(str(s).strip())
            if p <= 0:
                return None
            return p
        except Exception:
            return None

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
            tp = self._parse_percent(self.global_tp_percent_var.get())
            if tp is not None and growth_pct >= tp:
                self._trigger_global_stop(kind="TP", growth=growth_pct, limit=tp)
                return

        if sl_enabled:
            sl = self._parse_percent(self.global_sl_percent_var.get())
            if sl is not None and growth_pct <= -sl:
                self._trigger_global_stop(kind="SL", growth=growth_pct, limit=sl)
                return

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

# ------------------ Entry ------------------
if __name__ == "__main__":
    app = BotManagerApp(ui_poll_ms=100)
    app.run()