#!/usr/bin/env python3
"""
Terminal companion for the site's B = 100 prime family sweep.

Run with:
    python -m bridge_reptends.examples.prime_family_sweep_100
"""

from __future__ import annotations

from math import isqrt

from bridge_reptends import carried_prefix_visibility_profile, multiplicative_order


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    limit = isqrt(n)
    for candidate in range(3, limit + 1, 2):
        if n % candidate == 0:
            return False
    return True


def _regime(first_incoming_carry: int | None) -> str:
    if first_incoming_carry is None:
        return "no-carry"
    if first_incoming_carry >= 3:
        return "late-carry"
    return "early-carry"


def main() -> None:
    rows: list[dict[str, object]] = []
    for prime in range(3, 100, 2):
        if prime == 5 or not _is_prime(prime):
            continue
        profile = carried_prefix_visibility_profile(
            prime,
            base=10,
            n_blocks=8,
            prefer_m=2,
        )
        rows.append(
            {
                "prime": prime,
                "q": profile.q,
                "k": profile.k,
                "block_period": multiplicative_order(profile.B % prime, prime),
                "digit_period": profile.period,
                "first_incoming_carry": profile.first_incoming_carry_position,
                "raw_prefix_agreement_length": profile.raw_prefix_agreement_length,
                "regime": _regime(profile.first_incoming_carry_position),
                "visible_blocks": profile.actual_blocks[:6],
            }
        )

    rows.sort(
        key=lambda row: (
            row["first_incoming_carry"] is not None,
            -(row["first_incoming_carry"] if row["first_incoming_carry"] is not None else 99),
            int(row["k"]),
            int(row["prime"]),
        )
    )

    print("=" * 90)
    print("B = 100 PRIME FAMILY SWEEP")
    print("=" * 90)
    print("Fixed coordinate: B = 10^2 = 100")
    print("Columns: p, q, k = 100 mod p, ord_p(100), ord_p(10), first incoming carry, raw-prefix agreement")
    print()

    no_carry = sum(1 for row in rows if row["first_incoming_carry"] is None)
    late_carry = sum(
        1 for row in rows if row["first_incoming_carry"] is not None and int(row["first_incoming_carry"]) >= 3
    )
    early_carry = len(rows) - no_carry - late_carry
    print(f"summary: {len(rows)} primes, {no_carry} no-carry, {late_carry} late-carry, {early_carry} early-carry")
    print()

    for row in rows:
        carry_text = (
            "none"
            if row["first_incoming_carry"] is None
            else str(row["first_incoming_carry"])
        )
        visible_blocks = " ".join(f"{int(block):02d}" for block in row["visible_blocks"])
        print(
            f"p={int(row['prime']):>2}  "
            f"q={int(row['q']):>4}  "
            f"k={int(row['k']):>2}  "
            f"ord_p(100)={int(row['block_period']):>2}  "
            f"ord_p(10)={int(row['digit_period']):>2}  "
            f"carry={carry_text:>4}  "
            f"raw-agree={int(row['raw_prefix_agreement_length']):>2}  "
            f"regime={row['regime']:<10}  "
            f"blocks={visible_blocks}"
        )

    print()
    print("standouts:")
    for prime in (3, 11, 19, 97):
        row = next(row for row in rows if row["prime"] == prime)
        carry_text = (
            "none"
            if row["first_incoming_carry"] is None
            else str(row["first_incoming_carry"])
        )
        print(
            f"  p={prime}: q={row['q']}, k={row['k']}, ord_p(100)={row['block_period']}, "
            f"ord_p(10)={row['digit_period']}, first incoming carry={carry_text}, "
            f"visible blocks={' '.join(f'{int(block):02d}' for block in row['visible_blocks'])}"
        )


if __name__ == "__main__":
    main()
