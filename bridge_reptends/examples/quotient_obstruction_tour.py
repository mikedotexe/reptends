#!/usr/bin/env python3
"""
Guided visible-vs-hidden quotient-obstruction tour.

Run with:
    python -m bridge_reptends.examples.quotient_obstruction_tour
"""

from __future__ import annotations

from bridge_reptends import state_merging_rows, state_merging_same_core_rows


def _print_header(title: str) -> None:
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


def _print_case(n: int, prompt: str) -> None:
    row = next(row for row in state_merging_rows(n, base=10, n_blocks=8, max_m=8) if row["n"] == n)
    _print_header(f"Selected obstruction profile: 1/{n}")
    print(prompt)
    print()
    print(
        f"tuple (base=10, N={row['n']}, m={row['m']}, B={row['B']}, q={row['q']}, k={row['k']})"
    )
    print(f"selected regime:            {row['factorization_regime']}")
    print(f"obstruction class:          {row['obstruction_class']}")
    print(f"alignment bijection:        {row['observed_alignment_bijection']}")
    print(
        f"graph state gap:            {row['graph_state_gap']} "
        f"(carry={row['carry_state_count']}, remainder={row['remainder_state_count']})"
    )
    print(
        f"minimized class gap:        {row['minimized_class_gap']} "
        f"(carry={row['carry_class_count']}, remainder={row['remainder_class_count']})"
    )
    print(f"forward preimages:          {row['forward_preimage_signature']}")
    print(f"reverse ambiguities:        {row['reverse_ambiguity_signature']}")
    if row["compression_targets"]:
        targets = ", ".join(
            f"{entry['target_state']} <- {entry['source_states']}"
            for entry in row["compression_targets"]
        )
        print(f"visible compression targets: {targets}")
    else:
        print("visible compression targets: none")
    print(f"summary:                    {row['obstruction_summary']}")


def main() -> None:
    _print_header("Visible vs Hidden Quotient-Only Obstruction Tour")
    print("This tour keeps the visible/hidden split beneath the open carry factorization claim:")
    print("1. `21` is the relabeling baseline")
    print("2. `97` is visible prime compression")
    print("3. `89` is hidden prime obstruction")
    print("4. `996` is visible composite compression")
    print("5. `17 / 34 / 68 / 85` spans relabeling, hidden, and visible in one same-core family")

    _print_case(
        21,
        "The selected window stays bijective in both directions, so there is no quotient-only obstruction to classify.",
    )
    _print_case(
        97,
        "The forward map stays functional, but several remainder states visibly compress onto carry state `0` on the aligned window.",
    )
    _print_case(
        89,
        "The aligned window is bijective, so the failure is not visible in the fibers. The obstruction shows up only in the graph/class-count layer.",
    )
    _print_case(
        996,
        "The same visible compression pattern persists in a composite example with preperiod and same-core structure.",
    )

    family = next(
        row
        for row in state_merging_same_core_rows(1200, base=10, n_blocks=8, max_m=8)
        if row["core_n"] == 17
    )
    _print_header("Mixed same-core family: 17 / 34 / 68 / 85")
    print("This family keeps all three selected-coordinate outcomes visible on one stripped periodic core.")
    print(f"members:                     {family['members']}")
    print(f"selected regimes:            {family['selected_regimes']}")
    print(f"obstruction classes:         {family['selected_obstruction_classes']}")
    print(f"forward preimages:           {family['forward_preimage_signatures']}")
    print(f"reverse ambiguities:         {family['reverse_ambiguity_signatures']}")
    print(f"crosses relabeling/hidden/visible: {family['crosses_relabeling_hidden_visible_classes']}")


if __name__ == "__main__":
    main()
