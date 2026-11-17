# One balance check — v1.5.0

The changing-radix chapter now computes every digit from one signed balance, starting at the beginning of each example. It keeps the current radix when the proposed digit leaves a proper nonnegative remainder, accepts zero as completion, and changes the radix when a positive target needs a different unit.

The reader can compare the last kept step with the first switch, then follow eight continuation steps:

- **1/997:** write 729 in radix 998 after keeping the prefix through 243.
- **1/9899:** write 89 in radix 99, then 144 in radix 258. This Fibonacci example demonstrates both an oversized and a negative trial balance.
- **1/998001:** write 998 in radix 999 after keeping the counting prefix through 997.
- **Completion:** 1/8 = 0.125 keeps radix 10 and finishes at zero. Its bracket notation ends after [5], with optional zero padding.

The supplied progression determines the next target. The balance check determines whether to keep the current radix; the positive-target fallback supplies a valid replacement. Digit values use the product of all preceding radices as their weight. Ordinary notation continues to retain the exact fraction.

The atlas registers `unified_balance_rule` as `reproved-here`. `BalanceRule.lean` proves the signed check, legal digits, prefix/value preservation, completion, and convergence of the written stream. `BalanceContinue.lean` provides the positive continuation core and three concrete transition witnesses. All previous substantive proof modules are preserved unchanged. The full initial-prefix computations and browser are independently tested, not formally verified. The infinite-stream theorem assumes positive targets after any separately certified zero prefix; rejected zero targets need separate feasibility analysis.

Existing links remain valid. New `?hp=fibonacci` selects the third progression and `hp_step=0` selects the step before the switch. The main chapter and all three examples remain readable without JavaScript.
