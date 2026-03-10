"""
Composite-modulus and CRT analysis for repeating expansions.

The prime case has subgroup structure, but the periodicity itself is already
completely controlled by standard composite arithmetic:

1. Strip base factors from N to get the purely periodic modulus M.
2. Factor M into pairwise coprime prime powers.
3. Use CRT to analyze the remainder orbit componentwise.

For M = Π p_i^e_i with gcd(base, M) = 1:

    ord_M(base) = lcm_i ord_{p_i^e_i}(base)
    ord_M(base) | λ(M)

where λ is the Carmichael function.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, lcm

from .analysis import long_division_remainders, multiplicative_order
from .orbit_weave import (
    carmichael_lambda,
    factorize,
    find_good_modes,
    skeleton_vs_actual,
    strip_base_factors,
)
from .transducer import carry_remainder_comparison


@dataclass(frozen=True)
class PrimePowerPeriod:
    """Period data for one prime-power CRT component."""

    prime: int
    exponent: int
    modulus: int
    local_order: int
    local_lambda: int

    @property
    def local_order_divides_lambda(self) -> bool:
        if self.local_order == 0:
            return True
        return self.local_lambda % self.local_order == 0

    @property
    def lambda_quotient(self) -> int | None:
        if self.local_order == 0 or not self.local_order_divides_lambda:
            return None
        return self.local_lambda // self.local_order


@dataclass(frozen=True)
class PrimePowerLiftingStep:
    """One step in a prime-power lifting family p, p^2, ..., p^e."""

    prime: int
    exponent: int
    modulus: int
    local_order: int
    local_lambda: int
    previous_order: int | None
    stabilized_from_previous: bool

    @property
    def order_ratio_from_previous(self) -> int | None:
        if self.previous_order in (None, 0):
            return None
        return self.local_order // self.previous_order


@dataclass(frozen=True)
class PrimePowerLiftingFamily:
    """Order-lifting data for a fixed prime across successive exponents."""

    base: int
    prime: int
    steps: tuple[PrimePowerLiftingStep, ...]

    @property
    def stabilization_exponents(self) -> tuple[int, ...]:
        return tuple(step.exponent for step in self.steps if step.stabilized_from_previous)

    @property
    def strict_growth_exponents(self) -> tuple[int, ...]:
        return tuple(
            step.exponent
            for step in self.steps
            if step.previous_order is not None and step.local_order > step.previous_order
        )

    def summary_lines(self) -> tuple[str, ...]:
        lines = [f"prime-power lifting for p = {self.prime} in base {self.base}"]
        lines.extend(
            f"ord_{step.modulus}({self.base}) = {step.local_order}, lambda({step.modulus}) = {step.local_lambda}, "
            f"stabilized from previous = {step.stabilized_from_previous}"
            for step in self.steps
        )
        return tuple(lines)


@dataclass(frozen=True)
class CRTStep:
    """One step of the global remainder orbit and its CRT projections."""

    index: int
    remainder: int
    component_remainders: tuple[int, ...]


@dataclass(frozen=True)
class CRTPeriodProfile:
    """Composite period profile after stripping base factors."""

    N: int
    base: int
    stripped_modulus: int
    stripped_factors: dict[int, int]
    base_factorization: dict[int, int]
    preperiod_digits: int
    global_order: int
    carmichael_value: int
    components: tuple[PrimePowerPeriod, ...]

    @property
    def component_moduli(self) -> tuple[int, ...]:
        return tuple(component.modulus for component in self.components)

    @property
    def local_order_lcm(self) -> int:
        if not self.components:
            return 0
        order = 1
        for component in self.components:
            order = lcm(order, component.local_order)
        return order

    @property
    def order_equals_component_lcm(self) -> bool:
        return self.global_order == self.local_order_lcm

    @property
    def order_divides_carmichael(self) -> bool:
        if self.global_order == 0:
            return True
        return self.carmichael_value % self.global_order == 0

    @property
    def carmichael_quotient(self) -> int | None:
        if self.global_order == 0 or not self.order_divides_carmichael:
            return None
        return self.carmichael_value // self.global_order

    def summary_lines(self) -> tuple[str, ...]:
        if self.stripped_modulus == 1:
            return (
                f"N = {self.N}",
                f"base = {self.base}",
                "purely periodic modulus M = 1",
                f"preperiod length = {self.preperiod_digits} digit(s)",
            )

        component_terms = ", ".join(
            f"ord_{component.modulus}({self.base}) = {component.local_order}"
            for component in self.components
        )
        lambda_terms = ", ".join(
            f"lambda({component.modulus}) = {component.local_lambda}"
            for component in self.components
        )
        lines = [
            f"N = {self.N}, stripped modulus M = {self.stripped_modulus}",
            f"preperiod length = {self.preperiod_digits} digit(s)",
            f"component orders: {component_terms}",
            f"ord_M({self.base}) = lcm(component orders) = {self.global_order}",
            f"component Carmichael values: {lambda_terms}",
            f"lambda(M) = {self.carmichael_value}",
            f"order divides lambda(M): {self.order_divides_carmichael}",
        ]
        if self.carmichael_quotient is not None:
            lines.append(
                f"lambda(M) / ord_M({self.base}) = {self.carmichael_quotient}"
            )
        return tuple(lines)


@dataclass(frozen=True)
class CompositeCaseStudy:
    """Named composite example with both stripped-core and actual-coordinate data."""

    label: str
    family_id: str
    n: int
    profile: CRTPeriodProfile
    actual_m: int | None
    actual_k: int | None
    actual_q: int | None
    core_m: int | None
    core_k: int | None
    core_q: int | None
    crt_summary: str
    preperiod_summary: str
    carry_summary: str
    coordinate_summary: str
    carry_state_count: int
    carry_graph_class_count: int
    explanation: str


@dataclass(frozen=True)
class CompositeFamilyCaseStudy:
    """Family-level case study separating CRT, preperiod, carry, and coordinates."""

    label: str
    members: tuple[int, ...]
    primary_vocabulary_id: str
    crt_focus: str
    preperiod_focus: str
    carry_focus: str
    coordinate_focus: str
    explanation: str


def preperiod_length(n: int, base: int = 10) -> int:
    """
    Number of base digits before the repeating part begins.

    If base = Π p_i^{f_i}, then the preperiod length is

        max_i ceil(v_{p_i}(n) / f_i).
    """
    if n <= 0:
        return 0

    n_factors = factorize(n)
    base_factors = factorize(base)
    if not base_factors:
        return 0

    lengths = []
    for prime, base_exp in base_factors.items():
        exp = n_factors.get(prime, 0)
        if exp:
            lengths.append((exp + base_exp - 1) // base_exp)
    return max(lengths, default=0)


def prime_power_components(n: int) -> tuple[tuple[int, int, int], ...]:
    """
    Factor n as prime powers.

    Returns tuples (p, e, p^e), sorted by prime.
    """
    return tuple(
        (prime, exponent, prime ** exponent)
        for prime, exponent in sorted(factorize(n).items())
    )


def reconstruct_from_crt(residues: list[int] | tuple[int, ...], moduli: list[int] | tuple[int, ...]) -> int:
    """
    Reconstruct a residue class from pairwise coprime component moduli.
    """
    if len(residues) != len(moduli):
        raise ValueError("residues and moduli must have the same length")
    if not moduli:
        return 0

    modulus = 1
    for part in moduli:
        modulus *= part

    total = 0
    for residue, part in zip(residues, moduli):
        partial = modulus // part
        total += residue * partial * pow(partial, -1, part)
    return total % modulus


def crt_period_profile(n: int, base: int = 10) -> CRTPeriodProfile:
    """
    Compute the CRT decomposition of the purely periodic modulus of 1/n.
    """
    stripped_modulus, stripped_factors = strip_base_factors(n, base)
    base_factorization = factorize(base)
    preperiod_digits = preperiod_length(n, base)

    if stripped_modulus == 1:
        return CRTPeriodProfile(
            N=n,
            base=base,
            stripped_modulus=1,
            stripped_factors=stripped_factors,
            base_factorization=base_factorization,
            preperiod_digits=preperiod_digits,
            global_order=0,
            carmichael_value=1,
            components=(),
        )

    if gcd(stripped_modulus, base) != 1:
        raise ValueError(f"{stripped_modulus} is not coprime to base {base}")

    components = []
    local_orders = []
    for prime, exponent, modulus in prime_power_components(stripped_modulus):
        local_order = multiplicative_order(base, modulus)
        if local_order is None:
            raise ValueError(f"base {base} has no multiplicative order mod {modulus}")
        local_lambda = carmichael_lambda(modulus)
        components.append(
            PrimePowerPeriod(
                prime=prime,
                exponent=exponent,
                modulus=modulus,
                local_order=local_order,
                local_lambda=local_lambda,
            )
        )
        local_orders.append(local_order)

    global_order = 1
    for local_order in local_orders:
        global_order = lcm(global_order, local_order)

    direct_order = multiplicative_order(base, stripped_modulus)
    if direct_order is None:
        raise ValueError(f"base {base} has no multiplicative order mod {stripped_modulus}")
    assert global_order == direct_order

    return CRTPeriodProfile(
        N=n,
        base=base,
        stripped_modulus=stripped_modulus,
        stripped_factors=stripped_factors,
        base_factorization=base_factorization,
        preperiod_digits=preperiod_digits,
        global_order=global_order,
        carmichael_value=carmichael_lambda(stripped_modulus),
        components=tuple(components),
    )


def crt_remainder_orbit(n: int, base: int = 10, steps: int | None = None) -> list[CRTStep]:
    """
    Project the remainder orbit for 1/n to each CRT component.
    """
    profile = crt_period_profile(n, base)
    if profile.stripped_modulus == 1:
        return []

    orbit_steps = steps or profile.global_order
    remainders = long_division_remainders(profile.stripped_modulus, base, orbit_steps)
    moduli = profile.component_moduli
    rows = []
    for index, remainder in enumerate(remainders):
        residues = tuple(remainder % modulus for modulus in moduli)
        assert reconstruct_from_crt(residues, moduli) == remainder % profile.stripped_modulus
        rows.append(
            CRTStep(
                index=index,
                remainder=remainder,
                component_remainders=residues,
            )
        )
    return rows


def canonical_composite_case_studies(base: int = 10) -> tuple[CompositeCaseStudy, ...]:
    """
    Return the composite examples used throughout the docs and tests.

    The four default cases highlight distinct phenomena:
    - 21: CRT decomposition with k = 1 and no carry/preperiod
    - 27: prime-power modulus where ord is a strict divisor of lambda
    - 249: purely periodic composite core with small q and k
    - 996: same periodic core as 249 plus a nontrivial preperiod
    """
    examples = [
        (
            21,
            "CRT split with exact lambda",
            "two CRT components with local orders 1 and 6, so ord_M(base) = lambda(M) = 6; "
            "the small-residue block coordinate has k = 1, so the carry layer stays trivial",
        ),
        (
            27,
            "Prime-power strict Carmichael bound",
            "prime-power example where ord_M(base) = 3 is a strict divisor of lambda(M) = 18, "
            "showing that the Carmichael value is an upper bound rather than an equality in general",
        ),
        (
            249,
            "Composite periodic core",
            "purely periodic composite core with components 3 and 83; the 83-component carries the full period 41, "
            "while the small-residue block coordinate is 10^3 = 4*249 + 4",
        ),
        (
            996,
            "Preperiod plus periodic core",
            "same stripped periodic core as 249, but with a two-digit preperiod from the removed factor 2^2; "
            "the actual denominator still admits the bridge-style coordinate 10^3 = 1*996 + 4",
        ),
    ]

    rows: list[CompositeCaseStudy] = []
    for n, label, explanation in examples:
        profile = crt_period_profile(n, base)
        core_modes = (
            find_good_modes(profile.stripped_modulus, base=base, kmax=12, mmax=12, sort_by="k")
            if profile.stripped_modulus > 1
            else []
        )
        core_mode = core_modes[0] if core_modes else None
        actual_m = actual_k = actual_q = None
        if core_mode is not None:
            actual_view = skeleton_vs_actual(n, base=base, n_blocks=8, prefer_m=core_mode[0])
            actual_m = actual_view["m"]
            actual_k = actual_view["k"]
            actual_q = actual_view["q"]
        comparison = carry_remainder_comparison(
            n,
            base=base,
            n_blocks=8,
            prefer_m=actual_m,
        )
        component_summary = ", ".join(
            f"{component.modulus}:ord={component.local_order}:lambda={component.local_lambda}"
            for component in profile.components
        )

        rows.append(
            CompositeCaseStudy(
                label=label,
                family_id={
                    21: "clean-crt-split",
                    27: "prime-power-lifting",
                    249: "shared-periodic-core",
                    996: "shared-periodic-core",
                }[n],
                n=n,
                profile=profile,
                actual_m=actual_m,
                actual_k=actual_k,
                actual_q=actual_q,
                core_m=None if core_mode is None else core_mode[0],
                core_k=None if core_mode is None else core_mode[1],
                core_q=None if core_mode is None else core_mode[2],
                crt_summary=f"CRT local data: {component_summary}",
                preperiod_summary=f"preperiod length = {profile.preperiod_digits} digit(s)",
                carry_summary=(
                    f"carry states = {len(comparison.carry_graph.states)}, "
                    f"minimized classes = {comparison.minimized_carry_graph.class_count}, "
                    f"lookahead = {comparison.lookahead_blocks}"
                ),
                coordinate_summary=(
                    f"actual coordinate m = {actual_m}, q = {actual_q}, k = {actual_k}; "
                    f"periodic-core coordinate m = {None if core_mode is None else core_mode[0]}, "
                    f"q = {None if core_mode is None else core_mode[2]}, "
                    f"k = {None if core_mode is None else core_mode[1]}"
                ),
                carry_state_count=len(comparison.carry_graph.states),
                carry_graph_class_count=comparison.minimized_carry_graph.class_count,
                explanation=explanation,
            )
        )
    return tuple(rows)


def prime_power_lifting_family(prime: int, max_exponent: int, base: int = 10) -> PrimePowerLiftingFamily:
    """Return the order-lifting family for p, p^2, ..., p^e."""
    if prime <= 1 or max_exponent <= 0:
        raise ValueError("prime must exceed 1 and max_exponent must be positive")
    if gcd(prime, base) != 1:
        raise ValueError(f"prime {prime} must be coprime to base {base}")

    steps: list[PrimePowerLiftingStep] = []
    previous_order: int | None = None
    for exponent in range(1, max_exponent + 1):
        modulus = prime ** exponent
        local_order = multiplicative_order(base, modulus)
        if local_order is None:
            raise ValueError(f"base {base} has no multiplicative order mod {modulus}")
        steps.append(
            PrimePowerLiftingStep(
                prime=prime,
                exponent=exponent,
                modulus=modulus,
                local_order=local_order,
                local_lambda=carmichael_lambda(modulus),
                previous_order=previous_order,
                stabilized_from_previous=(previous_order == local_order),
            )
        )
        previous_order = local_order
    return PrimePowerLiftingFamily(base=base, prime=prime, steps=tuple(steps))


def canonical_composite_family_case_studies(base: int = 10) -> tuple[CompositeFamilyCaseStudy, ...]:
    """Return family-level composite case studies used by the docs and site."""
    lifting = prime_power_lifting_family(3, 4, base=base)
    cases = {case.n: case for case in canonical_composite_case_studies(base=base)}

    return (
        CompositeFamilyCaseStudy(
            label="Prime-power lifting at p = 3",
            members=tuple(step.modulus for step in lifting.steps),
            primary_vocabulary_id="remainder_orbit",
            crt_focus="single-component prime-power family where local order can stabilize before growing",
            preperiod_focus="no stripped base factors appear because every member is coprime to the base",
            carry_focus="carry stays secondary here; the main phenomenon is local order growth versus the Carmichael bound",
            coordinate_focus="small-residue coordinates exist, but the family is primarily about order lifting across 3, 9, 27, 81",
            explanation=(
                "This family shows a genuinely composite phenomenon: local orders on prime powers do not simply copy the prime case. "
                "For base 10, ord_3(10) = ord_9(10) = 1, then the order grows to 3 on 27 and 9 on 81."
            ),
        ),
        CompositeFamilyCaseStudy(
            label="Shared periodic core 249 / 996",
            members=(249, 996),
            primary_vocabulary_id="good_mode",
            crt_focus="both examples share the same CRT local orders because the purely periodic modulus is 249 in both cases",
            preperiod_focus="only 996 has a preperiod, coming from the stripped factor 2^2",
            carry_focus=(
                f"249 has {cases[249].carry_state_count} carry states while 996 has {cases[996].carry_state_count}; "
                "the carry layer changes, but the periodic core does not"
            ),
            coordinate_focus=(
                f"249 uses m = {cases[249].actual_m}, q = {cases[249].actual_q}, k = {cases[249].actual_k}; "
                f"996 uses m = {cases[996].actual_m}, q = {cases[996].actual_q}, k = {cases[996].actual_k}"
            ),
            explanation=(
                "This family separates the purely periodic remainder-orbit structure from the base-factor preperiod. "
                "The pair is the clearest composite example where CRT data, preperiod length, and carry normalization can be discussed independently."
            ),
        ),
    )
