#!/usr/bin/env python3
"""
Guided orbit-plus-carry tour for the repo's flagship throughline.

Run with:
    python -m bridge_reptends.examples.orbit_plus_carry_tour
"""

from __future__ import annotations

from bridge_reptends import (
    carry_remainder_comparison,
    multiplicative_order,
    skeleton_vs_actual,
)


def _print_header(title: str) -> None:
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


def _print_case(
    *,
    n: int,
    prefer_m: int,
    title: str,
    prompt: str,
) -> None:
    comparison = skeleton_vs_actual(n, base=10, n_blocks=8, prefer_m=prefer_m)
    factorization = carry_remainder_comparison(n, base=10, n_blocks=8, prefer_m=prefer_m)
    periodic_modulus = int(comparison["M"])
    block_period = multiplicative_order(int(comparison["B"]), periodic_modulus)

    _print_header(f"{title}: 1/{n}")
    print(prompt)
    print()
    print(
        "tuple "
        f"(base=10, N={n}, M={periodic_modulus}, m={comparison['m']}, "
        f"B={comparison['B']}, q={comparison['q']}, k={comparison['k']}, L={block_period})"
    )
    if periodic_modulus != n:
        print(f"preperiod/core split: actual denominator {n} descends to periodic core {periodic_modulus}")
    print(f"raw coefficients:     {comparison['raw'][:8]}")
    print(f"raw display blocks:   {comparison['raw_display'][:8]}")
    print(f"carry-normalized:     {list(factorization.carry_example.carried_blocks[:8])}")
    print(f"long-division blocks: {list(factorization.carry_example.actual_blocks[:8])}")
    print(f"lookahead used:       {factorization.lookahead_blocks}")
    print(f"finite-window outputs match: {factorization.outputs_match}")
    print(
        "observed state maps: "
        f"remainder->carry functional={factorization.remainder_to_carry_map.is_functional}, "
        f"carry->remainder functional={factorization.carry_to_remainder_map.is_functional}"
    )
    print(f"decision regime:      {factorization.decision_report.regime}")
    print(f"implemented layer:    {factorization.implemented_statement}")
    print(f"open frontier:        {factorization.open_claim_boundary}")


def main() -> None:
    _print_header("Orbit + Carry Tour")
    print("This ladder keeps the repo's flagship thesis status-honest:")
    print("1. exact remainder-orbit support")
    print("2. exact block-coordinate support")
    print("3. implemented finite-window carry normalization")
    print("4. open frontier: canonical global orbit-plus-carry factorization")

    _print_case(
        n=21,
        prefer_m=6,
        title="Carry Layer Collapses",
        prompt=(
            "The remainder orbit is already periodic, the raw coefficient stream is constant, "
            "and the carry machine collapses to one state."
        ),
    )
    _print_case(
        n=97,
        prefer_m=2,
        title="Orbit Law Clean, Carry Turns On Later",
        prompt=(
            "This is the canonical decimal q = 1 coordinate: the raw layer begins as literal "
            "powers of k, and the incoming carry appears only after several clean orbit steps."
        ),
    )
    _print_case(
        n=996,
        prefer_m=3,
        title="Preperiod / Composite Layer Meets The Same Frontier",
        prompt=(
            "Base-supported factors create a finite decimal preperiod, but the periodic core "
            "still exposes the same orbit-plus-carry split and the same open factorization boundary."
        ),
    )


if __name__ == "__main__":
    main()
