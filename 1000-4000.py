# Updated 1000-4000.py

class SmoothDrawdownPayoutStrategy:
    def _get_drawdown_L(self, current_balance):
        # Existing logic without internal get_current_balance call
        drawdown_L = ...  # logic using current_balance
        return drawdown_L

    # Existing methods

# Inside the relevant function

def update_strategy(strategy, current_balance):
    payout = strategy.next_payout_and_bet(current_balance)
    return payout

class BotTab:
    def start_bot(self, smooth_factory):
        # Previous code
        payout_min = self.UI.get_min_payout()
        payout_max = self.UI.get_max_payout()
        smooth_factory(payout_min=payout_min, payout_max=payout_max)
        # Rest of the existing code