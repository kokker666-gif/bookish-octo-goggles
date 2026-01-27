# Original content of crypto_games_bot_stable_100-9999_norm_versiya_Version36_Version10.py
# Integrating SmoothDrawdownPayoutStrategy changes as per the requirements:

class SmoothDrawdownPayoutStrategy:
    def __init__(self, initial_payout=1000, max_payout=9999):
        self.current_payout = initial_payout
        self.max_payout = max_payout
        self.target_pct_ramp = 0.25
        self.target_pct_max = 0.5
        self.L = range(51)  # Reset range from 0 to 50

    def update_payout(self, win):
        if win:
            # If a win occurs at maximum payout, reset payout
            if self.current_payout >= self.max_payout:
                self.current_payout = self.initial_payout
            else:
                # Adjust payout based on the drawdown strategy
                self.current_payout = min(self.max_payout, self.current_payout * (1 + self.target_pct_ramp))
        else:
            # Decrease payout according to your logic
            self.current_payout = self.initial_payout  # Example logic, modify as needed

# Additional existing logic and GUI functions here...

# Existing functionalities and logic from previous iterations of the bot should be included here.