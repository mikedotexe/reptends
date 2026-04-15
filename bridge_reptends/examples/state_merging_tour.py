#!/usr/bin/env python3
"""
Guided preimage-fiber profile tour for the state-merging atlas.

Run with:
    python -m bridge_reptends.examples.state_merging_tour
"""

from __future__ import annotations

from bridge_reptends import state_merging_rows, state_merging_same_core_rows


def _print_header(title: str) -> None:
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


def _print_case(n: int, prompt: str) -> None:
    row = next(row for row in state_merging_rows(n, base=10, n_blocks=8, max_m=8) if row["n"] == n)
    _print_header(f"Selected state-merging profile: 1/{n}")
    print(prompt)
    print()
    print(
        f"tuple (base=10, N={row['n']}, m={row['m']}, B={row['B']}, q={row['q']}, k={row['k']})"
    )
    print(f"selected regime:      {row['factorization_regime']}")
    print(f"forward preimages:    {row['forward_preimage_signature']}")
    print(f"reverse ambiguities:  {row['reverse_ambiguity_signature']}")
    print(
        f"forward functional:   {row['forward_profile']['is_functional']}, "
        f"injective: {row['forward_profile']['is_injective']}"
    )
    print(
        f"reverse functional:   {row['reverse_profile']['is_functional']}, "
        f"injective: {row['reverse_profile']['is_injective']}"
    )
    print("alignment rows:")
    for alignment in row["alignment_rows"][:8]:
        print(
            "  "
            f"j={alignment['position']}  coeff={alignment['coefficient']}  "
            f"remainder={alignment['remainder_state']}  carry={alignment['carry_state']}  "
            f"block={alignment['block_value']}"
        )


def main() -> None:
    _print_header("Preimage-Fiber Profile Tour")
    print("This tour keeps the state-merging atlas beneath the open carry factorization claim:")
    print("1. `21` shows the one-state relabeling baseline")
    print("2. `97` shows quotient-only prime collapse")
    print("3. `996` shows quotient-only composite collapse")
    print("4. `249 -> 996` keeps the same-core reverse obstruction explicit")

    _print_case(
        21,
        "The selected window is fully symmetric: both directions stay bijective, so the compression story disappears into a trivial relabeling.",
    )
    _print_case(
        97,
        "Several remainder states collapse onto carry state `0`, so the forward direction remains functional while the reverse direction visibly fails.",
    )
    _print_case(
        996,
        "The same forward-only compression persists even with preperiod and same-core structure in view.",
    )

    same_core = next(
        row
        for row in state_merging_same_core_rows(1200, base=10, n_blocks=8, max_m=8)
        if row["core_n"] == 249
    )
    _print_header("Same-core obstruction: 249 / 498 / 996")
    print("This family keeps the state-compression disagreement visible on one stripped periodic core.")
    print(f"members:                {same_core['members']}")
    print(f"selected regimes:       {same_core['selected_regimes']}")
    print(f"forward preimages:      {same_core['forward_preimage_signatures']}")
    print(f"reverse ambiguities:    {same_core['reverse_ambiguity_signatures']}")
    print(f"same-core disagreement: {same_core['has_state_merging_disagreement']}")


if __name__ == "__main__":
    main()
