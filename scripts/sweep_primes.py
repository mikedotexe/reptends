#!/usr/bin/env python3
"""
CLI wrapper for sweep-primes command.

This is a thin wrapper that calls bridge_reptends.sweep.main().
The actual implementation is in bridge_reptends/sweep.py.

Usage:
    python scripts/sweep_primes.py --max 500 --bases 2,7,10,12

Or if installed:
    sweep-primes --max 500 --bases 2,7,10,12
"""

if __name__ == "__main__":
    from bridge_reptends.sweep import main
    main()
