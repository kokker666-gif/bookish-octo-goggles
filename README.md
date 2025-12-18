# bookish-octo-goggles

**[Русская версия / Russian version](README_RU.md)**

## Cryptocurrency Arbitrage Script

This repository includes `crypto_arbitrage.py`, a Python script that fetches cryptocurrency prices from multiple exchanges and identifies arbitrage opportunities.

### Features

1. **Multi-Exchange Price Fetching**: Fetches BTC/USD prices from three major exchanges:
   - Binance (BTC/USDT)
   - Coinbase (BTC/USD)
   - Kraken (BTC/USD)

2. **Arbitrage Detection**: Identifies profitable arbitrage opportunities by:
   - Finding the lowest ask price (where to buy)
   - Finding the highest bid price (where to sell)
   - Calculating potential profit percentage

3. **Error Handling**: Robust error handling for:
   - API connectivity issues
   - Network timeouts
   - JSON parsing errors
   - Graceful degradation when exchanges are unavailable

### Installation

Install the required dependencies:

```bash
pip install -r requirements.txt
```

### Usage

Run the arbitrage script:

```bash
python crypto_arbitrage.py
```

The script will:
1. Fetch current BTC prices from all available exchanges
2. Display bid and ask prices for each exchange
3. Identify the best arbitrage opportunity
4. Calculate and display potential profit percentage
5. Indicate whether a profitable arbitrage exists

### Example Output

```
Binance: Bid=50000.00, Ask=50010.00
Coinbase: Bid=50005.00, Ask=50015.00
Kraken: Bid=50002.00, Ask=50012.00

Prices: {'Binance': (50000.0, 50010.0), 'Coinbase': (50005.0, 50015.0), 'Kraken': (50002.0, 50012.0)}

Arbitrage Opportunity:
Buy from Binance at 50010.00 and sell to Coinbase at 50005.00
Potential profit: -0.01%
✗ No profitable arbitrage opportunity (sell price <= buy price)
```

### Notes

- The script uses public API endpoints that don't require authentication
- Network access is required to fetch live prices
- Arbitrage opportunities in cryptocurrency markets are typically small and short-lived
- Transaction fees and withdrawal limits are not considered in the profit calculation