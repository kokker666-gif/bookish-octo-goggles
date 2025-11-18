def _cover50_bet(self, payout: Decimal, current_balance: Decimal) -> Decimal | None:
    dd = self._calc_cover_drawdown(current_balance)
    if dd <= 0:
        return None
    target_profit = dd * Decimal("0.50")
    bet = compute_covering_bet_for_target(
        payout,
        target_profit,
        self.min_bet or Decimal("0.001"),
        self.config.max_bet_limit,
        current_balance,
        house_edge_frac=self.house_edge_frac,        # <-- учитываем edge
        margin_ratio=self.cover_margin_ratio         # <-- добавляем +3%
    )
    # кап по банку (как и раньше)
    try:
        cap_by_bank = quantize_bet(self.cover50_cap_ratio * current_balance)
        if bet > cap_by_bank:
            bet = cap_by_bank
    except Exception:
        pass
    if bet < self.min_bet:
        bet = self.min_bet
    return bet