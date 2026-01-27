# Updated code with minimum changes as specified

class SmoothDrawdownPayoutStrategy:
    def _get_drawdown_L(self, current_balance):
        # Previous implementation had self._bot.get_current_balance()
        # New implementation uses current_balance directly.
        pass  # replace with actual logic using current_balance

class CryptoGamesBot:
    def start(self, state):
        # Other logic...
        current_balance = state['current_balance']
        self.strategy.next_payout_and_bet(state, current_balance)

class BotTab:
    def start_bot(self, payout_min, payout_max):
        # Passing values from UI instead of static values
        smooth_factory = SmoothDrawdownPayoutStrategy(payout_min=payout_min, payout_max=payout_max)
        # Other code remains unchanged...