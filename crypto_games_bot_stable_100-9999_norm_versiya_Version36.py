# Updated Crypto Games Bot

## Changes Made:
1. **LinearPayoutStrategy Adjustments**:
   - Modified wrap handling:
     - If a circle had at least one WIN, `target_pct` increases by +0.25 for each winning circle up to a maximum of 1.0.
     - If a circle had no WIN, `target_pct` halves or initializes to 1.0 if it was 0.
   - Maintains tracking of `circle_had_win`.

2. **Win Reset Behavior**:
   - Removed `on_win_reset` handling tied to any win. Resets only `loss_sum` as before.

3. **BetConfig Defaults**:
   - Set the following defaults:
     - `coin='LTC'`
     - `base_bet=0.00001`
     - `min_bet_enforced=0.00001`
   - Keep `SIM_DEFAULT_INITIAL_BANK` as is.

4. **References and UI Updates**:
   - Ensured any references or UI default for coin and enforced min default entries reflect `LTC` and `0.00001`.