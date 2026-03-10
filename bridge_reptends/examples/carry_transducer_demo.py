#!/usr/bin/env python3
"""
Carry-transducer demo for small canonical examples.

Run with:
    python -m bridge_reptends.examples.carry_transducer_demo
"""

from ..transducer import carry_window_example


def print_example(n: int, *, prefer_m: int, n_blocks: int) -> None:
    example = carry_window_example(n, prefer_m=prefer_m, n_blocks=n_blocks)
    summary = example.run.state_summary()

    print("=" * 72)
    print(f"N = {n}, m = {example.m}, B = {example.B}, q = {example.q}, k = {example.k}")
    print("=" * 72)
    print(f"raw coefficients:   {list(example.raw_coefficients[:8])}")
    print(f"carried blocks:     {list(example.carried_blocks[:8])}")
    print(f"long-division view: {list(example.actual_blocks[:8])}")
    print(f"reachable carries:  {summary.reachable_states}")
    print(f"first nonzero carry position: {summary.first_nonzero_position}")
    print(f"matches long division: {example.matches_long_division}")
    print("sample transitions:")
    for transition in example.run.transitions[: min(8, len(example.run.transitions))]:
        print(
            f"  pos {transition.position:>2}: "
            f"coeff={transition.coefficient:>6}, "
            f"carry_in={transition.carry_in:>4}, "
            f"block={transition.block_value:>4}, "
            f"carry_out={transition.carry_out:>4}"
        )
    print()


def main() -> None:
    print_example(21, prefer_m=6, n_blocks=6)
    print_example(97, prefer_m=2, n_blocks=8)
    print_example(996, prefer_m=3, n_blocks=8)


if __name__ == "__main__":
    main()
