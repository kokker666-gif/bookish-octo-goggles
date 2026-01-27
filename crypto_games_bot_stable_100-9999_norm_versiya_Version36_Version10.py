class SmoothDrawdownPayoutStrategy:
    def __init__(self):
        self.last_successful_bank = 0
        self.target_pct = 0.25  # default when L < 50

    def calculate_payout(self, L):
        if L < 50:
            self.target_pct = 0.25
        else:
            self.target_pct = 0.5

        payout_amount = min(1000 + (9999 - 1000) * (L / 50), 9999)
        return payout_amount

    def after_win(self):
        # Force the next payout after winning
        self.last_successful_bank = 1000
        self.target_pct = 0.25

class BotTab:
    def start_bot(self):
        # Use SmoothDrawdownPayoutStrategy instead of LinearPayoutStrategy
        payout_strategy = SmoothDrawdownPayoutStrategy() 
        # ... rest of the code
    
# Existing code below
