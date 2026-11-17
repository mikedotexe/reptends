# Mixed-radix run notation

This is the specification used by [the live chapter](https://reptends.mikedotexe.com/#change-radix). The [proof-status atlas](../docs/PROOF_STATUS_ATLAS.md#mixed_radix_run_value_preservation) registers the underlying run accounting as `reproved-here`. The bracket notation, serializer, and browser are `implemented-here`, not formally verified programs.

## Reading a run

`⟨d1, d2, ..., dL⟩_B` means L successive fractional digits, each using integer radix B ≥ 2. Every digit is an integer in [0, B). Commas separate digit positions; a multi-digit decimal label such as 2187 is still one digit in its stated radix. Initial zeros count as positions. The integers are spelled in decimal for readability, independently of their mathematical radices.

`0.` starts the fractional representation. `|` marks a change of radix, not necessarily a remainder return. A single-digit run has the same syntax as a longer run. Runs of one radix may be split or combined without changing their weighted value; the displayed examples combine adjacent uses of the same radix.

Each digit has weight 1 divided by the product of all radices used through that digit. A run of length L uses its radix L times. If the previous place product is P and H is the Horner-packed integer `d1*B^(L-1) + ... + dL`, the run contributes `H/(P*B^L)`.

An ellipsis inside the counting prefix means every consecutive integer between the shown endpoints. A final ellipsis means continue the specified generator and balance policy. A finite excerpt is a prefix with an unresolved tail, not an exact finite equality to the whole fraction.

## The balance policy

For a proper fraction A/D, start with `P=1, Q=0, r=A`, an initial radix B ≥ 2, and a supplied sequence of target terms. The invariant is:

```text
D*Q+r = A*P
A/D = Q/P + r/(D*P)
```

For the next term a ≥ 0, with 0 < r < D, compute signed `T=B*r-D*a`.

- `0 < T < D`: keep B, emit a, continue with remainder T.
- `T=0`: keep B, emit a, and finish. Later positional digits may only be zero.
- `T<0` or `T>=D`, with a > 0: use `R=floor(D*a/r)+1` and remainder `R*r-D*a`. This is the smallest radix emitting that digit with a **positive** remainder. It is not claimed to be the smallest radix if zero remainder is also allowed.

The update using the chosen radix R is `P'=P*R`, `Q'=R*Q+a`, `r'=R*r-D*a`. Initial zero terms that pass the balance check are supported. A rejected zero target requires separate feasibility analysis; the positive-target fallback is not valid for it. When the incoming remainder is already zero, the expansion is complete.

The progression is an explicit input. For the examples below it is the coefficient progression from the original reciprocal series. The fraction alone does not specify a unique progression. Changing the radix changes later place weights; ordinary positional notation still retains the exact value.

## Three worked examples

Indices of the coefficient sequences start at zero; displayed digit positions start at one.

| Fraction | Original radix | Generator | Preserved run | First changed digit / radix |
| --- | --- | --- | --- | --- |
| 1/997 | 1000 | a(0)=1, a(n+1)=3a(n) | 1,3,9,27,81,243 (6 digits) | 729 / 998 |
| 1/9899 | 100 | a(0)=0, a(1)=1, a(n+2)=a(n+1)+a(n) | 0,1,1,2,3,5,8,13,21,34,55 (11 digits) | 89 / 99 |
| 1/998001 | 1000 | a(0)=0, a(n+1)=a(n)+1 | every integer 0 through 997 (998 digits) | 998 / 999 |

```text
1/997:
0.⟨1,3,9,27,81,243⟩_1000 | ⟨729⟩_998 | ⟨2187⟩_2992 | ⟨6561⟩_8974 | ...

1/9899:
0.⟨0,1,1,2,3,5,8,13,21,34,55⟩_100 | ⟨89⟩_99 | ⟨144⟩_258 | ⟨233⟩_996 | ...

1/998001:
0.⟨0,1,2,...,997⟩_1000 | ⟨998⟩_999 | ⟨999⟩_998002 | ⟨1000⟩_999001 | ...
```

For example, the first changed contribution in 1/997 is `729/(1000^6*998)`. The original prefix keeps its value and every new radix multiplies the place product. The three series have denominators B−3, B²−B−1, and (B−1)² at their original radices. Only the first coefficient sequence is geometric; the same balance policy handles all three.

The first switches occur at digit positions 7, 12, and 999, discovered by the balance check from the start. They are not defined by a cycle boundary. In ordinary decimal 1/997 the period is 166 decimal digits; a 166-group base-1000 loop spans 498 decimal positions. Later powers still contribute through carries to those endpoints.

Completion is allowed: `1/8 = 0.⟨1,2,5⟩_10`. After the last digit the remainder is zero, so the representation may stop or pad with zeros in the same radix.

The optional from-start power construction has different weights: radix `997*3^n+1` writes `3^n` with remainder 1. Its old `?run=` links remain supported. It is separate from the main policy that preserves the original base-1000 prefix.

## Proof map and limits

| Mathematical meaning | Lean source and theorems |
| --- | --- |
| Digits in a run equal their Horner-packed and weighted value | [Encoding.lean](../lean/RadixRuns/Encoding.lean): `RadixRuns.Run.packed_eq_horner`, `RadixRuns.Run.digitValue_eq_packed` |
| A run contributes H/(P B^L); runs and radix changes preserve exact value | [Core.lean](../lean/RadixRuns/Core.lean): `RadixRuns.DivisionState.advance_prefix_value`, `advance_value`, `radix_change_preserves_value` |
| Balance choices write legal digits and preserve the prefix certificate | [BalanceRule.lean](../lean/RadixRuns/BalanceRule.lean): `RadixBalance.chosen_digit_legal`, `chosen_preserves_prefix`, `chosen_preserves_value` |
| Zero finishes; the actual written stream retains the fraction's value | [BalanceRule.lean](../lean/RadixRuns/BalanceRule.lean): `RadixBalance.zero_finishes`, `completed_stays_completed`, `stream_hasSum`, `after_prefix_hasSum` |

The generic stream theorem assumes positive targets after any separately certified initial zeros. It pads with zero digits after completion. It does not assert that an arbitrary positive generator continues to be emitted after completion. Initial prefix computations, JSON, and browser behavior are independently tested, not Lean-certified implementations. No uniqueness or historical novelty is claimed.

## Structured page data

The self-contained HTML embeds `script#reptends-notation`, `type="application/json"`, schema version 1. It can be read from the HTML without executing JavaScript. Its top-level fields are `grammar`, `semantics`, `policy`, `claims`, `limitations`, and `examples` (plus format metadata).

Each example gives the numerator, denominator, initial radix, generator seeds and recurrence, complete digit arrays for the preserved run and eight following runs, and the corresponding balance decisions. Arithmetic integers are decimal strings; lengths and one-based positions are JSON numbers. No ellipses occur in the digit arrays. Each changed step records the current radix, signed trial balance, chosen radix, requested digit, and before/after remainders. The data can be checked by ordinary integer division and the invariant above.

The existing `script#reptends-certificate` remains a separate record for ordinary decimal cycles and carries. Neither JSON record is itself a proof-assistant certificate.
