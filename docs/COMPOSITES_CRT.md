# Composite / CRT Generalization

Status anchor:

- Claim ID `crt_period_lcm` is `classical`.
- Preferred standard label: `remainder orbit under multiplication by the base`.

This is the right entry point for composites. The prime case adds QR/NQR structure, but the periodicity itself is already controlled by standard CRT arithmetic.

## Exact Period Relations

Let `N` be any denominator and strip the base factors to get the purely periodic modulus `M`. Write

`M = Π p_i^{e_i}` with `gcd(base, M) = 1`.

Then the exact global period is

`ord_M(base) = lcm_i ord_{p_i^{e_i}}(base)`.

The Carmichael function gives the universal exponent bound

`ord_M(base) | λ(M)`.

Equality with `λ(M)` can happen, but it is not automatic. The point of the composite API is to expose both the exact `lcm` formula and the usually larger Carmichael bound in the same object.

## Canonical Cases

The helper [canonical_composite_case_studies()](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py) packages the repository’s four standard examples.

| `N` | `M` after stripping base factors | Preperiod | Local orders | `ord_M(10)` | `λ(M)` | Why it matters |
|---|---:|---:|---|---:|---:|---|
| `21` | `21` | `0` | `ord_3(10)=1`, `ord_7(10)=6` | `6` | `6` | Small `k=1` CRT split with exact equality `ord = λ` |
| `27` | `27` | `0` | `ord_27(10)=3` | `3` | `18` | Prime-power case where `λ(M)` is a strict upper bound |
| `249` | `249` | `0` | `ord_3(10)=1`, `ord_83(10)=41` | `41` | `82` | Purely periodic composite core with readable `q=4, k=4` coordinate |
| `996` | `249` | `2` | same as `249` | `41` | `82` | Same periodic core as `249`, but with a two-digit preperiod from `2^2` |

## What the API Exposes

In [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py):

- `crt_period_profile(N, base)` gives the stripped modulus, local prime-power factors, local orders, global order, and `λ(M)`.
- `CRTPeriodProfile.local_order_lcm` exposes the exact `lcm` reconstruction directly.
- `CRTPeriodProfile.order_divides_carmichael` and `CRTPeriodProfile.carmichael_quotient` make the order-vs-`λ` relation explicit.
- `PrimePowerPeriod.lambda_quotient` makes the local order-vs-`λ(p^e)` gap explicit on each CRT component.
- `CRTPeriodProfile.summary_lines()` renders the exact order and Carmichael data in standard notation.
- `canonical_composite_case_studies()` returns the named `21`, `27`, `249`, `996` examples with separate CRT, preperiod, carry, and coordinate summaries.
- `prime_power_lifting_family(p, e)` exposes how the local order behaves across `p, p^2, ..., p^e`.
- `canonical_composite_family_case_studies()` packages the two family-level stories the repo now emphasizes: prime-power lifting at `p = 3`, and the shared periodic core `249 / 996`.

Minimal example:

```python
from bridge_reptends import canonical_composite_case_studies

for case in canonical_composite_case_studies():
    print(case.label, case.n)
    for line in case.profile.summary_lines():
        print(" ", line)
    print(" ", case.crt_summary)
    print(" ", case.preperiod_summary)
    print(" ", case.carry_summary)
    print(" ", case.coordinate_summary)
    print(" ", case.explanation)
```

## Composite Families

The repo now treats two family-level stories as canonical.

### Prime-power lifting at `3, 9, 27, 81`

This is the cleanest small family where composite structure adds something the prime case does not.

- `ord_3(10) = 1`
- `ord_9(10) = 1`
- `ord_27(10) = 3`
- `ord_81(10) = 9`

So the local order can stabilize for one lift and then grow. That is a prime-power phenomenon, not a prime-field one.

### Shared periodic core `249 / 996`

These two denominators share the same purely periodic modulus `249`, so they have the same CRT local orders and the same global period.

- `249` shows the periodic core directly.
- `996` adds a two-digit preperiod from the removed factor `2^2`.
- the carry layer changes between them, but the periodic core does not.

## Why `249` and `996` Belong Together

`996 = 2^2 * 249`, so the repeating part is governed by the same coprime core `249`.

- `249` is the purely periodic core.
- `996` has the same component orders and the same global period.
- The only extra phenomenon is the preperiod length `2`, caused by the removed factor `2^2`.

That is why the repo treats `249` and `996` as a matched pair rather than unrelated examples.

## Why `21` and `27` Are Also Needed

`249` and `996` are the best medium-size examples, but they are not sufficient by themselves.

- `21` is the cleanest small composite with an actual CRT split and `k = 1`, so it shows the decomposition without any carry noise.
- `27` is the cleanest small prime-power example where `ord_M(base)` is strictly smaller than `λ(M)`, so it prevents the false impression that Carmichael equality is typical.

Together, `21`, `27`, `249`, and `996` cover the composite phenomena the repo actually uses.
