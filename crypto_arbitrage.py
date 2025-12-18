#!/usr/bin/env python3
"""
Cryptocurrency Arbitrage Script

This script fetches cryptocurrency prices from three different exchanges 
(Binance, Coinbase, Kraken) and checks for arbitrage opportunities.

Features:
1. Fetch cryptocurrency prices for BTC/USD from multiple exchanges
2. Calculate and display arbitrage opportunities
3. Provide error handling for API connectivity issues
"""

import requests

BINANCE_URL = "https://api.binance.com/api/v3/ticker/bookTicker?symbol=BTCUSDT"
COINBASE_URL = "https://api.pro.coinbase.com/products/BTC-USD/book"
KRAKEN_URL = "https://api.kraken.com/0/public/Ticker?pair=XBTUSD"

# Fetch price from Binance
def fetch_binance_price():
    """
    Fetch BTC/USDT price from Binance exchange.
    
    Returns:
        tuple: (bid_price, ask_price)
    
    Raises:
        Exception: If API request fails
    """
    try:
        response = requests.get(BINANCE_URL, timeout=10)
        response.raise_for_status()
        data = response.json()
        return float(data['bidPrice']), float(data['askPrice'])
    except requests.exceptions.RequestException as e:
        print(f"Error fetching Binance price: {e}")
        raise
    except (KeyError, ValueError) as e:
        print(f"Error parsing Binance data: {e}")
        raise

# Fetch price from Coinbase
def fetch_coinbase_price():
    """
    Fetch BTC/USD price from Coinbase exchange.
    
    Returns:
        tuple: (bid_price, ask_price)
    
    Raises:
        Exception: If API request fails
    """
    try:
        response = requests.get(COINBASE_URL, timeout=10)
        response.raise_for_status()
        data = response.json()
        bid = float(data['bids'][0][0])
        ask = float(data['asks'][0][0])
        return bid, ask
    except requests.exceptions.RequestException as e:
        print(f"Error fetching Coinbase price: {e}")
        raise
    except (KeyError, ValueError, IndexError) as e:
        print(f"Error parsing Coinbase data: {e}")
        raise

# Fetch price from Kraken
def fetch_kraken_price():
    """
    Fetch BTC/USD price from Kraken exchange.
    
    Returns:
        tuple: (bid_price, ask_price)
    
    Raises:
        Exception: If API request fails
    """
    try:
        response = requests.get(KRAKEN_URL, timeout=10)
        response.raise_for_status()
        data = response.json()
        pair = data['result']['XXBTZUSD']
        bid = float(pair['b'][0])
        ask = float(pair['a'][0])
        return bid, ask
    except requests.exceptions.RequestException as e:
        print(f"Error fetching Kraken price: {e}")
        raise
    except (KeyError, ValueError, IndexError) as e:
        print(f"Error parsing Kraken data: {e}")
        raise

# Find arbitrage opportunities
def find_arbitrage():
    """
    Find arbitrage opportunities by comparing prices across exchanges.
    
    This function fetches prices from all three exchanges and identifies
    where to buy low and sell high for potential profit.
    """
    prices = {}
    
    # Fetch prices with error handling
    try:
        prices["Binance"] = fetch_binance_price()
        print(f"Binance: Bid={prices['Binance'][0]}, Ask={prices['Binance'][1]}")
    except Exception as e:
        print(f"Failed to fetch Binance prices: {e}")
    
    try:
        prices["Coinbase"] = fetch_coinbase_price()
        print(f"Coinbase: Bid={prices['Coinbase'][0]}, Ask={prices['Coinbase'][1]}")
    except Exception as e:
        print(f"Failed to fetch Coinbase prices: {e}")
    
    try:
        prices["Kraken"] = fetch_kraken_price()
        print(f"Kraken: Bid={prices['Kraken'][0]}, Ask={prices['Kraken'][1]}")
    except Exception as e:
        print(f"Failed to fetch Kraken prices: {e}")
    
    if len(prices) < 2:
        print("Error: Not enough exchanges available for arbitrage comparison")
        return
    
    print("\nPrices:", prices)
    
    # Identify arbitrage opportunities among exchanges
    # For arbitrage: buy at lowest ask price, sell at highest bid price
    buy_from = min(prices, key=lambda x: prices[x][1])  # Lowest ask (buying price)
    sell_to = max(prices, key=lambda x: prices[x][0])  # Highest bid (selling price)
    
    buy_price = prices[buy_from][1]  # Ask price (price to buy at)
    sell_price = prices[sell_to][0]  # Bid price (price to sell at)
    
    print(f"\nArbitrage Opportunity:")
    print(f"Buy from {buy_from} at {buy_price} and sell to {sell_to} at {sell_price}")
    
    # Calculate potential profit percentage
    if buy_price > 0:
        profit_percentage = ((sell_price - buy_price) / buy_price) * 100
        print(f"Potential profit: {profit_percentage:.2f}%")
        
        if sell_price > buy_price:
            print("✓ Profitable arbitrage opportunity exists!")
        else:
            print("✗ No profitable arbitrage opportunity (sell price <= buy price)")

if __name__ == "__main__":
    find_arbitrage()
