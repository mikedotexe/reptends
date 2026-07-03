"""
Exact observables for carried-prefix visibility.

Track 16 sharpens the open carried-prefix question into concrete finite-window
objects. For a chosen denominator and block coordinate, the repo now separates:

- the raw coefficient stream q*k^j,
- the local overflow boundary where q*k^j first stops fitting in one block,
- the first incoming-carry position where later overflow changes an earlier
  visible block,
- the exact raw-prefix agreement length, and
- the minimal lookahead needed to stabilize a requested visible window.

The open claim is no longer "visibility" in the abstract. It is the search for
an arithmetic formula for these exact observables in terms of q, k, B, and the
period data.
"""

from __future__ import annotations

from dataclasses import dataclass

from .composite import crt_period_profile
from .registry import claim_context_for_parameters
from .transducer import (
    CarryTransition,
    carry_remainder_comparison,
    carry_window_example,
    same_core_obstruction_phase_rows,
    state_merging_rows,
)


def _first_local_overflow_position(raw_coefficients: tuple[int, ...], block_base: int) -> int | None:
    for index, coefficient in enumerate(raw_coefficients):
        if coefficient >= block_base:
            return index
    return None


def _first_incoming_carry_position(
    transitions: tuple[CarryTransition, ...],
    requested_blocks: int,
) -> int | None:
    for transition in transitions[:requested_blocks]:
        if transition.carry_in > 0:
            return transition.position
    return None


def _raw_block_strings(raw_coefficients: tuple[int, ...], *, block_base: int, width: int) -> tuple[str, ...]:
    blocks: list[str] = []
    for coefficient in raw_coefficients:
        if coefficient < block_base:
            blocks.append(str(coefficient).zfill(width))
        else:
            blocks.append(f"[{coefficient}]")
    return tuple(blocks)


def _leading_raw_agreement(raw_coefficients: tuple[int, ...], actual_blocks: tuple[str, ...], *, block_base: int, width: int) -> int:
    count = 0
    for coefficient, block in zip(raw_coefficients, actual_blocks):
        if coefficient >= block_base:
            break
        if str(coefficient).zfill(width) != block:
            break
        count += 1
    return count


def _position_or_window(position: int | None, requested_blocks: int) -> int:
    return requested_blocks if position is None else position


def _power_exponent(base: int, value: int) -> int | None:
    if value <= 0:
        return None
    if base == 1:
        return 0 if value == 1 else None
    if base <= 0:
        return None
    exponent = 0
    current = value
    while current > 1 and current % base == 0:
        current //= base
        exponent += 1
    return exponent if current == 1 else None


def _floor_log_base(base: int, value: int) -> int:
    if base <= 1 or value <= 0:
        raise ValueError("base must exceed 1 and value must be positive")
    exponent = 0
    current = 1
    while current * base <= value:
        current *= base
        exponent += 1
    return exponent


def _shift_endpoint_label(shift: int | None, interval: tuple[int, int] | None) -> str | None:
    if shift is None or interval is None:
        return None
    lower, upper = interval
    if lower == upper == shift:
        return "exact"
    if shift == lower:
        return "lower"
    if shift == upper:
        return "upper"
    return "interior"


def incoming_carry_value(q: int, k: int, B: int, position: int) -> int:
    """
    Exact incoming carry into block `position` for the infinite q*k^j stream.

    The tail beyond position j is:

        Σ_{t>=1} q*k^(j+t) / B^t = q*k^(j+1) / (B-k)

    so the incoming carry is its integer part.
    """
    if position < 0:
        raise ValueError("position must be nonnegative")
    if q <= 0 or k <= 0 or B <= 1 or k >= B:
        return 0
    return (q * pow(k, position + 1)) // (B - k)


def predicted_first_incoming_carry_position(
    q: int,
    k: int,
    B: int,
    *,
    requested_blocks: int | None = None,
) -> int | None:
    """Predict the first block that receives positive incoming carry."""
    if q <= 0 or k <= 0 or B <= 1 or k >= B:
        return None
    threshold = B - k
    term = q * k
    position = 0
    limit = requested_blocks if requested_blocks is not None else None
    while term < threshold:
        if limit is not None and position + 1 >= limit:
            return None
        if k == 1:
            return None
        term *= k
        position += 1
    return position


def predicted_raw_prefix_agreement_length(
    q: int,
    k: int,
    B: int,
    *,
    requested_blocks: int,
) -> int:
    """Predict the exact raw-prefix agreement length from the two boundaries."""
    first_overflow = _first_local_overflow_position(tuple(q * pow(k, j) for j in range(requested_blocks)), B)
    first_incoming = predicted_first_incoming_carry_position(
        q,
        k,
        B,
        requested_blocks=requested_blocks,
    )
    return min(
        _position_or_window(first_overflow, requested_blocks),
        _position_or_window(first_incoming, requested_blocks),
    )


def lookahead_tail_mass_lower_bound(
    q: int,
    k: int,
    B: int,
    *,
    requested_blocks: int,
) -> int:
    """
    Necessary lower bound for stabilization lookahead.

    If the omitted tail after `requested_blocks + L - 1` still contributes at
    least one full block unit to the visible prefix integer, stabilization is
    impossible. This yields the necessary condition

        q*k^(n+L) < B^L * (B-k).
    """
    if q <= 0 or k <= 0 or B <= 1 or k >= B:
        return 0
    lookahead = 0
    while q * pow(k, requested_blocks + lookahead) >= pow(B, lookahead) * (B - k):
        lookahead += 1
    return lookahead


def lookahead_gap_numerator(
    q: int,
    k: int,
    B: int,
    *,
    requested_blocks: int,
    lookahead_blocks: int,
) -> int:
    """
    Numerator of the gap from the truncated prefix to the next integer.

    If

        B^n * Σ_{j=0}^{n+L-1} q*k^j / B^(j+1) = I + r / B^L

    with 0 <= r < B^L, then the gap numerator is B^L - r (or B^L when r = 0).
    """
    if lookahead_blocks < 0:
        raise ValueError("lookahead_blocks must be nonnegative")
    if lookahead_blocks == 0:
        return 1
    fractional_numerator = 0
    for offset in range(lookahead_blocks):
        fractional_numerator = (fractional_numerator * B) + q * pow(k, requested_blocks + offset)
    modulus = pow(B, lookahead_blocks)
    remainder = fractional_numerator % modulus
    return modulus if remainder == 0 else modulus - remainder


def lookahead_certificate_holds(
    q: int,
    k: int,
    B: int,
    *,
    requested_blocks: int,
    lookahead_blocks: int,
) -> bool:
    """
    Exact finite-window stabilization certificate.

    The first `requested_blocks` blocks stabilize after `lookahead_blocks = L`
    exactly when the omitted tail is smaller than the gap from the truncated
    prefix to the next integer.
    """
    gap_numerator = lookahead_gap_numerator(
        q,
        k,
        B,
        requested_blocks=requested_blocks,
        lookahead_blocks=lookahead_blocks,
    )
    return q * pow(k, requested_blocks + lookahead_blocks) < gap_numerator * (B - k)


def certified_lookahead_blocks(
    q: int,
    k: int,
    B: int,
    *,
    requested_blocks: int,
    max_lookahead_blocks: int = 128,
) -> int:
    """Least lookahead satisfying the exact prefix-gap certificate."""
    lower_bound = lookahead_tail_mass_lower_bound(
        q,
        k,
        B,
        requested_blocks=requested_blocks,
    )
    for lookahead in range(lower_bound, max_lookahead_blocks + 1):
        if lookahead_certificate_holds(
            q,
            k,
            B,
            requested_blocks=requested_blocks,
            lookahead_blocks=lookahead,
        ):
            return lookahead
    raise ValueError(
        f"lookahead certificate did not hold within {max_lookahead_blocks} extra block(s)"
    )


@dataclass(frozen=True)
class VisibilityProfile:
    """Exact finite-window visibility data for one denominator."""

    n: int
    periodic_modulus: int
    base: int
    m: int
    B: int
    q: int
    k: int
    period: int
    preperiod_digits: int
    requested_blocks: int
    lookahead_blocks: int
    lookahead_lower_bound: int
    certified_lookahead_blocks: int
    raw_coefficients: tuple[int, ...]
    raw_blocks: tuple[str, ...]
    actual_blocks: tuple[str, ...]
    first_local_overflow_position: int | None
    first_incoming_carry_position: int | None
    predicted_first_incoming_carry_position: int | None
    raw_prefix_agreement_length: int
    predicted_raw_prefix_agreement_length: int
    exact_gap_numerator: int

    @property
    def first_mismatch_position(self) -> int | None:
        if self.raw_prefix_agreement_length >= self.requested_blocks:
            return None
        return self.raw_prefix_agreement_length

    @property
    def full_window_visible(self) -> bool:
        return self.raw_prefix_agreement_length == self.requested_blocks

    @property
    def mismatch_regime(self) -> str:
        if self.full_window_visible:
            return "fully_visible_window"
        if self.first_incoming_carry_position is not None and (
            self.first_local_overflow_position is None
            or self.first_incoming_carry_position < self.first_local_overflow_position
        ):
            return "incoming_carry_before_local_overflow"
        return "local_overflow_boundary"

    @property
    def agreement_identity_holds(self) -> bool:
        return self.predicted_raw_prefix_agreement_length == self.raw_prefix_agreement_length

    @property
    def incoming_carry_formula_holds(self) -> bool:
        return self.predicted_first_incoming_carry_position == self.first_incoming_carry_position

    @property
    def lookahead_certificate_matches(self) -> bool:
        return self.certified_lookahead_blocks == self.lookahead_blocks

    @property
    def theorem_candidate(self) -> str:
        return (
            "Extend the exact incoming-carry boundary formula to useful closed-form lower and "
            "upper bounds for stabilization lookahead."
        )

    @property
    def heuristic_note(self) -> str:
        return (
            "Small k, and especially q = 1, often increases the raw-prefix agreement length, "
            "but that remains heuristic rather than theorem-level."
        )

    @property
    def counterexample_target(self) -> str:
        return (
            "Look for examples where incoming carry arrives strictly before the local overflow "
            "boundary, refuting naive q*k^j < B visibility rules."
        )

    def summary_lines(self) -> tuple[str, ...]:
        return (
            f"N = {self.n}, periodic modulus = {self.periodic_modulus}, base = {self.base}",
            f"block width m = {self.m}, block base B = {self.B}, q = {self.q}, k = {self.k}",
            f"period = {self.period}, preperiod digits = {self.preperiod_digits}",
            f"raw-prefix agreement length = {self.raw_prefix_agreement_length}",
            f"first local overflow position = {self.first_local_overflow_position}",
            f"first incoming carry position = {self.first_incoming_carry_position}",
            f"predicted incoming carry position = {self.predicted_first_incoming_carry_position}",
            f"lookahead lower bound = {self.lookahead_lower_bound}",
            f"minimal stabilization lookahead = {self.lookahead_blocks}",
            f"certified stabilization lookahead = {self.certified_lookahead_blocks}",
            f"exact gap numerator at that lookahead = {self.exact_gap_numerator}",
            f"mismatch regime = {self.mismatch_regime}",
            (
                "implemented relation: agreement length = min(local overflow boundary, "
                "incoming-carry boundary)"
            ),
            f"incoming-carry formula holds on this case = {self.incoming_carry_formula_holds}",
            f"raw-prefix formula holds on this case = {self.agreement_identity_holds}",
            f"lookahead certificate matches on this case = {self.lookahead_certificate_matches}",
        )


@dataclass(frozen=True)
class VisibilityCaseStudy:
    """Named example used to track the visibility problem."""

    label: str
    family_id: str
    profile: VisibilityProfile
    explanation: str
    theorem_candidate: str
    heuristic_note: str
    counterexample_target: str

    @property
    def n(self) -> int:
        return self.profile.n


@dataclass(frozen=True)
class VisibilityFamilyStudy:
    """Named family for the Track 16 research program."""

    label: str
    members: tuple[int, ...]
    explanation: str
    theorem_candidate: str
    heuristic_note: str
    counterexample_target: str
    primary_vocabulary_id: str
    summary_lines: tuple[str, ...] = ()


@dataclass(frozen=True)
class SameCoreVisibilityComparison:
    """Comparison between an actual denominator and its stripped periodic core."""

    actual_profile: VisibilityProfile
    core_profile: VisibilityProfile
    shared_bridge_defect: int
    q_ratio: int | None
    q_ratio_floor_log_k: int | None
    q_ratio_k_exponent: int | None
    incoming_carry_shift_matches: bool
    local_overflow_shift_matches: bool
    raw_prefix_shift_matches: bool

    @property
    def lookahead_shift(self) -> int:
        return self.core_profile.certified_lookahead_blocks - self.actual_profile.certified_lookahead_blocks

    @property
    def exact_shift_law_holds(self) -> bool:
        return (
            self.q_ratio_k_exponent is not None
            and self.incoming_carry_shift_matches
            and self.local_overflow_shift_matches
            and self.raw_prefix_shift_matches
        )

    @property
    def shift_interval(self) -> tuple[int, int] | None:
        if self.q_ratio_floor_log_k is None:
            return None
        lower = self.q_ratio_floor_log_k
        upper = self.q_ratio_floor_log_k if self.q_ratio_k_exponent is not None else self.q_ratio_floor_log_k + 1
        return (lower, upper)

    def allowed_shift_interval(self, actual_boundary: int) -> tuple[int, int] | None:
        if self.shift_interval is None:
            return None
        lower, upper = self.shift_interval
        return (min(actual_boundary, lower), min(actual_boundary, upper))

    @staticmethod
    def _shift_value(actual_boundary: int | None, core_boundary: int | None) -> int | None:
        if actual_boundary is None or core_boundary is None:
            return None
        return actual_boundary - core_boundary

    @property
    def incoming_carry_shift(self) -> int | None:
        return self._shift_value(
            self.actual_profile.first_incoming_carry_position,
            self.core_profile.first_incoming_carry_position,
        )

    @property
    def local_overflow_shift(self) -> int | None:
        return self._shift_value(
            self.actual_profile.first_local_overflow_position,
            self.core_profile.first_local_overflow_position,
        )

    @property
    def raw_prefix_shift(self) -> int | None:
        return self._shift_value(
            self.actual_profile.raw_prefix_agreement_length,
            self.core_profile.raw_prefix_agreement_length,
        )

    def threshold_shift_interval_holds(self, actual_boundary: int | None, core_boundary: int | None) -> bool:
        shift = self._shift_value(actual_boundary, core_boundary)
        if shift is None or actual_boundary is None:
            return False
        interval = self.allowed_shift_interval(actual_boundary)
        if interval is None:
            return False
        lower, upper = interval
        return lower <= shift <= upper

    @property
    def incoming_carry_interval_holds(self) -> bool:
        return self.threshold_shift_interval_holds(
            self.actual_profile.first_incoming_carry_position,
            self.core_profile.first_incoming_carry_position,
        )

    @property
    def local_overflow_interval_holds(self) -> bool:
        return self.threshold_shift_interval_holds(
            self.actual_profile.first_local_overflow_position,
            self.core_profile.first_local_overflow_position,
        )

    @property
    def raw_prefix_interval_holds(self) -> bool:
        return self.threshold_shift_interval_holds(
            self.actual_profile.raw_prefix_agreement_length,
            self.core_profile.raw_prefix_agreement_length,
        )

    @property
    def interval_family_law_holds(self) -> bool:
        return (
            self.incoming_carry_interval_holds
            and self.local_overflow_interval_holds
            and self.raw_prefix_interval_holds
        )

    @property
    def common_threshold_shift(self) -> int | None:
        shifts = [
            shift
            for shift in (
                self.incoming_carry_shift,
                self.local_overflow_shift,
                self.raw_prefix_shift,
            )
            if shift is not None
        ]
        if not shifts or len(set(shifts)) != 1:
            return None
        return shifts[0]

    @property
    def threshold_shift_endpoint(self) -> str | None:
        return _shift_endpoint_label(self.common_threshold_shift, self.shift_interval)

    def summary_lines(self) -> tuple[str, ...]:
        return (
            f"actual/core = {self.actual_profile.n}/{self.core_profile.n}",
            f"shared B = {self.actual_profile.B}, shared k = {self.actual_profile.k}, shared B-k = {self.shared_bridge_defect}",
            f"q_actual = {self.actual_profile.q}, q_core = {self.core_profile.q}, q_ratio = {self.q_ratio}",
            f"floor_log_k(q_ratio) = {self.q_ratio_floor_log_k}",
            f"q_ratio as power of k = {self.q_ratio_k_exponent}",
            f"incoming-carry positions actual/core = {self.actual_profile.first_incoming_carry_position}/{self.core_profile.first_incoming_carry_position}",
            f"local-overflow positions actual/core = {self.actual_profile.first_local_overflow_position}/{self.core_profile.first_local_overflow_position}",
            f"raw-prefix agreement actual/core = {self.actual_profile.raw_prefix_agreement_length}/{self.core_profile.raw_prefix_agreement_length}",
            f"certified lookahead actual/core = {self.actual_profile.certified_lookahead_blocks}/{self.core_profile.certified_lookahead_blocks}",
            f"threshold shift interval law holds = {self.interval_family_law_holds}",
            f"threshold shift endpoint = {self.threshold_shift_endpoint}",
            f"exact k-power shift law holds = {self.exact_shift_law_holds}",
        )


def _same_core_mode_priority(comparison: SameCoreVisibilityComparison) -> tuple[int, int, int, int, int, int]:
    interval_nonpower = int(not (
        comparison.interval_family_law_holds
        and comparison.q_ratio is not None
        and comparison.q_ratio_k_exponent is None
    ))
    endpoint_rank = {
        "upper": 0,
        "lower": 1,
        "exact": 2,
        "interior": 3,
        None: 4,
    }[comparison.threshold_shift_endpoint]
    positive_shift = int((comparison.common_threshold_shift or 0) <= 0)
    return (
        interval_nonpower,
        endpoint_rank,
        positive_shift,
        comparison.actual_profile.k,
        comparison.actual_profile.m,
        comparison.actual_profile.B,
    )


def select_same_core_prefer_m(
    n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_m: int = 12,
    max_block_base: int = 100_000,
    require_interval_law: bool = True,
) -> int | None:
    """
    Pick a shared block coordinate that best exposes the same-core family law.

    Unlike the generic small-residue selector, this intentionally favors
    non-power interval-law examples when they exist, since those carry more
    information about the broader family than a purely exact k-power case.
    """
    best: tuple[tuple[int, int, int, int, int, int], int] | None = None
    for m in range(1, max_m + 1):
        try:
            comparison = same_core_visibility_comparison(
                n,
                base=base,
                n_blocks=n_blocks,
                prefer_m=m,
            )
        except Exception:
            continue
        if comparison.actual_profile.n == comparison.core_profile.n:
            continue
        if comparison.actual_profile.q <= 0 or comparison.actual_profile.k <= 1:
            continue
        if comparison.actual_profile.B > max_block_base:
            continue
        if require_interval_law and not comparison.interval_family_law_holds:
            continue
        candidate = (_same_core_mode_priority(comparison), m)
        if best is None or candidate < best:
            best = candidate
    return None if best is None else best[1]


def carried_prefix_visibility_profile(
    n: int,
    *,
    base: int = 10,
    n_blocks: int = 12,
    prefer_m: int | None = None,
    max_lookahead_blocks: int = 128,
) -> VisibilityProfile:
    """Compute the exact finite-window visibility observables for one example."""
    example = carry_window_example(
        n,
        base=base,
        n_blocks=n_blocks,
        prefer_m=prefer_m,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    profile = crt_period_profile(n, base)
    raw_coefficients = example.raw_coefficients[:n_blocks]
    raw_blocks = _raw_block_strings(raw_coefficients, block_base=example.B, width=example.m)
    first_local_overflow = _first_local_overflow_position(raw_coefficients, example.B)
    first_incoming_carry = _first_incoming_carry_position(example.run.transitions, n_blocks)
    agreement_length = _leading_raw_agreement(
        raw_coefficients,
        example.actual_blocks[:n_blocks],
        block_base=example.B,
        width=example.m,
    )
    predicted_incoming = predicted_first_incoming_carry_position(
        example.q,
        example.k,
        example.B,
        requested_blocks=n_blocks,
    )
    predicted_agreement = predicted_raw_prefix_agreement_length(
        example.q,
        example.k,
        example.B,
        requested_blocks=n_blocks,
    )
    lookahead_lower_bound = lookahead_tail_mass_lower_bound(
        example.q,
        example.k,
        example.B,
        requested_blocks=n_blocks,
    )
    certified_lookahead = certified_lookahead_blocks(
        example.q,
        example.k,
        example.B,
        requested_blocks=n_blocks,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    exact_gap_numerator = lookahead_gap_numerator(
        example.q,
        example.k,
        example.B,
        requested_blocks=n_blocks,
        lookahead_blocks=certified_lookahead,
    )
    return VisibilityProfile(
        n=n,
        periodic_modulus=profile.stripped_modulus,
        base=base,
        m=example.m,
        B=example.B,
        q=example.q,
        k=example.k,
        period=profile.global_order,
        preperiod_digits=profile.preperiod_digits,
        requested_blocks=n_blocks,
        lookahead_blocks=example.lookahead_blocks,
        lookahead_lower_bound=lookahead_lower_bound,
        certified_lookahead_blocks=certified_lookahead,
        raw_coefficients=raw_coefficients,
        raw_blocks=raw_blocks,
        actual_blocks=example.actual_blocks[:n_blocks],
        first_local_overflow_position=first_local_overflow,
        first_incoming_carry_position=first_incoming_carry,
        predicted_first_incoming_carry_position=predicted_incoming,
        raw_prefix_agreement_length=agreement_length,
        predicted_raw_prefix_agreement_length=predicted_agreement,
        exact_gap_numerator=exact_gap_numerator,
    )


def canonical_visibility_case_studies(base: int = 10) -> tuple[VisibilityCaseStudy, ...]:
    """Return the canonical Track 16 visibility cases."""
    cases = [
        (
            "Carry-free constant window",
            "q-positive-family",
            21,
            6,
            6,
            "q is large but k = 1, so every requested raw block is already legal and no incoming carry appears.",
        ),
        (
            "Positive-q constant coefficient window",
            "q-positive-family",
            37,
            3,
            6,
            "q > 1 and k = 1 give a constant raw coefficient stream, making this the cleanest non-bridge positive-q case.",
        ),
        (
            "Incoming carry before local overflow",
            "q-one-family",
            97,
            2,
            8,
            "The displayed block at position 4 changes because of incoming carry even though the local raw coefficient 81 is still below 100.",
        ),
        (
            "Positive-q carry intrusion",
            "q-positive-family",
            249,
            3,
            8,
            "The positive-q case already exhibits early incoming carry, so naive q*k^j < B visibility rules fail outside q = 1 as well.",
        ),
        (
            "Shared periodic core with preperiod",
            "shared-periodic-core",
            996,
            3,
            8,
            "This shares the periodic core of 249 but adds a decimal preperiod, separating periodic-core structure from visible-prefix behavior.",
        ),
    ]
    return tuple(
        VisibilityCaseStudy(
            label=label,
            family_id=family_id,
            profile=carried_prefix_visibility_profile(
                n,
                base=base,
                n_blocks=n_blocks,
                prefer_m=prefer_m,
            ),
            explanation=explanation,
            theorem_candidate="Extend the exact incoming-carry boundary to useful bounds for stabilization lookahead and same-core families.",
            heuristic_note="Small k still correlates with longer readable raw prefixes, but the exact boundary is not yet a theorem.",
            counterexample_target="Use this case family to test and refute naive visibility rules based only on local overflow.",
        )
        for label, family_id, n, prefer_m, n_blocks, explanation in cases
    )


def canonical_visibility_family_studies(base: int = 10) -> tuple[VisibilityFamilyStudy, ...]:
    """Return the canonical Track 16 family-level study prompts."""
    same_core_exact = same_core_visibility_comparison(996, base=base, n_blocks=8, prefer_m=3)
    same_core_interval = same_core_visibility_comparison(498, base=base, n_blocks=8, prefer_m=3)
    families = [
        VisibilityFamilyStudy(
            label="q = 1 carried-prefix family",
            members=(97, 996),
            explanation="Both cases have q = 1 and small k, but one is prime-purely-periodic and the other has a decimal preperiod. Compare raw-prefix agreement length and lookahead rather than only k.",
            theorem_candidate="Use the exact incoming-carry boundary as a base case for proving lookahead bounds in the q = 1 bridge regime.",
            heuristic_note="q = 1 often gives unusually readable early blocks, but 996 shows that preperiod and tail carry still matter.",
            counterexample_target="Rule out any visibility criterion that ignores preperiod data once the same q = 1 residue pattern appears in both pure and preperiodic settings.",
            primary_vocabulary_id="carry_layer",
        ),
        VisibilityFamilyStudy(
            label="q > 1 carried-prefix family",
            members=(21, 37, 249),
            explanation="These cases separate positive-q constant windows from positive-q early-carry intrusion, so q > 1 by itself is not a visibility obstruction.",
            theorem_candidate="Determine how q interacts with k and B in quantitative lookahead bounds once the incoming-carry boundary is fixed exactly.",
            heuristic_note="Large q can still be perfectly legible when k = 1, while moderate q with k > 1 can fail early.",
            counterexample_target="Refute any criterion that treats q > 1 as automatically unreadable.",
            primary_vocabulary_id="good_mode",
        ),
        VisibilityFamilyStudy(
            label="Shared periodic core with different preperiods",
            members=(249, 498, 996),
            explanation="This family isolates one periodic core while varying the stripped base-factor ratio. The comparison 996/249 shows the exact k-power shift law, while 498/249 shows the broader two-point interval law when the q-ratio is not itself a power of k.",
            theorem_candidate="Classify same-core families by q-ratio intervals between consecutive powers of k, and separate which observables satisfy exact shift laws versus interval laws.",
            heuristic_note="The periodic core strongly constrains k and B-k, but lookahead and preperiod behavior still depend on the actual denominator.",
            counterexample_target="Test any proposed same-core formula on both the exact-power case 996/249 and the non-power case 498/249.",
            primary_vocabulary_id="remainder_orbit",
            summary_lines=same_core_exact.summary_lines() + ("---",) + same_core_interval.summary_lines(),
        ),
    ]
    if base == 10:
        base7_exact = same_core_visibility_comparison(56, base=7, n_blocks=8, prefer_m=3)
        base12_lower = same_core_visibility_comparison(10, base=12, n_blocks=8, prefer_m=2)
        base12_upper = same_core_visibility_comparison(70, base=12, n_blocks=8, prefer_m=2)
        base12_exact = same_core_visibility_comparison(20, base=12, n_blocks=8, prefer_m=2)
        families.extend(
            [
                VisibilityFamilyStudy(
                    label="Cross-base same-core exact law",
                    members=(8, 56),
                    explanation="Base 7 supplies a non-decimal exact-law family: in the shared coordinate B = 343 and k = 7, the pair 56/8 realizes the same one-block exact shift seen in the decimal 996/249 family.",
                    theorem_candidate="Show which same-core exact-shift laws depend only on the shared q-ratio power relation and not on the ambient base.",
                    heuristic_note="Exact k-power shift laws appear across bases once a shared coordinate with small k is fixed.",
                    counterexample_target="Test whether any claimed exact same-core law survives after changing base while preserving the q-ratio power relation.",
                    primary_vocabulary_id="remainder_orbit",
                    summary_lines=base7_exact.summary_lines(),
                ),
                VisibilityFamilyStudy(
                    label="Cross-base interval endpoints in one coordinate",
                    members=(5, 10, 20, 35, 70),
                    explanation="Base 12 exhibits all three local same-core outcomes in one shared coordinate B = 144, k = 4: 10/5 realizes the lower interval endpoint, 70/35 realizes the upper interval endpoint, and 20/5 realizes the exact k-power law.",
                    theorem_candidate="Classify which interval-law endpoints can occur in a fixed shared coordinate before any exact global lookahead formula is available.",
                    heuristic_note="A single shared coordinate can realize lower-endpoint, upper-endpoint, and exact-shift behavior across different actual/core pairs.",
                    counterexample_target="Reject any family claim that only tests one endpoint of the interval law or only exact k-power ratios.",
                    primary_vocabulary_id="remainder_orbit",
                    summary_lines=base12_lower.summary_lines()
                    + ("---",)
                    + base12_upper.summary_lines()
                    + ("---",)
                    + base12_exact.summary_lines(),
                ),
            ]
        )
    return tuple(families)


def same_core_visibility_comparison(
    n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    prefer_m: int | None = None,
) -> SameCoreVisibilityComparison:
    """Compare a denominator to its stripped periodic core in the same block coordinate."""
    if prefer_m is None:
        prefer_m = select_same_core_prefer_m(
            n,
            base=base,
            n_blocks=n_blocks,
        )
    actual = carried_prefix_visibility_profile(
        n,
        base=base,
        n_blocks=n_blocks,
        prefer_m=prefer_m,
    )
    core = carried_prefix_visibility_profile(
        actual.periodic_modulus,
        base=base,
        n_blocks=n_blocks,
        prefer_m=actual.m,
    )
    shared_bridge_defect = actual.B - actual.k
    q_ratio = None
    q_ratio_floor_log_k = None
    q_ratio_k_exponent = None
    if actual.q > 0 and core.q % actual.q == 0:
        q_ratio = core.q // actual.q
        if actual.k > 1:
            q_ratio_floor_log_k = _floor_log_base(actual.k, q_ratio)
        elif q_ratio == 1:
            q_ratio_floor_log_k = 0
        q_ratio_k_exponent = _power_exponent(actual.k, q_ratio)

    def _shift_match(actual_boundary: int | None, core_boundary: int | None) -> bool:
        if q_ratio_k_exponent is None:
            return False
        if actual_boundary is None and core_boundary is None:
            return True
        if actual_boundary is None or core_boundary is None:
            return False
        return core_boundary == max(actual_boundary - q_ratio_k_exponent, 0)

    return SameCoreVisibilityComparison(
        actual_profile=actual,
        core_profile=core,
        shared_bridge_defect=shared_bridge_defect,
        q_ratio=q_ratio,
        q_ratio_floor_log_k=q_ratio_floor_log_k,
        q_ratio_k_exponent=q_ratio_k_exponent,
        incoming_carry_shift_matches=_shift_match(
            actual.first_incoming_carry_position,
            core.first_incoming_carry_position,
        ),
        local_overflow_shift_matches=_shift_match(
            actual.first_local_overflow_position,
            core.first_local_overflow_position,
        ),
        raw_prefix_shift_matches=_shift_match(
            actual.raw_prefix_agreement_length,
            core.raw_prefix_agreement_length,
        ),
    )


def visibility_profile_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    kmax: int = 6,
    mmax: int = 12,
) -> list[dict[str, object]]:
    """
    Export exact visibility observables for small-residue block coordinates.

    This is the Track 16 dataset layer: measured examples and counterexample
    targets rather than theorem-level claims.
    """
    rows: list[dict[str, object]] = []
    for n in range(2, max_n + 1):
        try:
            profile = carried_prefix_visibility_profile(n, base=base, n_blocks=n_blocks)
        except ValueError:
            continue
        if profile.periodic_modulus == 1:
            continue
        if profile.k > kmax or profile.m > mmax or profile.q <= 0:
            continue
        rows.append(
            {
                "n": profile.n,
                "periodic_modulus": profile.periodic_modulus,
                "base": profile.base,
                "m": profile.m,
                "B": profile.B,
                "q": profile.q,
                "k": profile.k,
                "period": profile.period,
                "preperiod_digits": profile.preperiod_digits,
                "requested_blocks": profile.requested_blocks,
                "lookahead_lower_bound": profile.lookahead_lower_bound,
                "raw_prefix_agreement_length": profile.raw_prefix_agreement_length,
                "predicted_raw_prefix_agreement_length": profile.predicted_raw_prefix_agreement_length,
                "first_local_overflow_position": profile.first_local_overflow_position,
                "first_incoming_carry_position": profile.first_incoming_carry_position,
                "predicted_first_incoming_carry_position": profile.predicted_first_incoming_carry_position,
                "lookahead_blocks": profile.lookahead_blocks,
                "certified_lookahead_blocks": profile.certified_lookahead_blocks,
                "exact_gap_numerator": profile.exact_gap_numerator,
                "mismatch_regime": profile.mismatch_regime,
                "incoming_carry_formula_holds": profile.incoming_carry_formula_holds,
                "agreement_identity_holds": profile.agreement_identity_holds,
                "lookahead_certificate_matches": profile.lookahead_certificate_matches,
                **claim_context_for_parameters(
                    (
                        "incoming_carry_position_formula",
                        "small_k_visibility_threshold",
                        "small_k_visibility_heuristic",
                    ),
                    base=profile.base,
                    n=profile.n,
                    requested_blocks=profile.requested_blocks,
                ),
            }
        )
    rows.sort(
        key=lambda row: (
            row["mismatch_regime"] != "incoming_carry_before_local_overflow",
            -int(row["raw_prefix_agreement_length"]),
            int(row["k"]),
            int(row["n"]),
        )
    )
    return rows


CERTIFIED_POSITIVE_LOOKAHEAD_STATUS_ORDER = {
    "covered_by_gap_one_bridge": 0,
    "empirically_coefficient_functional_frontier": 1,
    "coefficient_functionality_counterexample_candidate": 2,
}


def _certified_positive_lookahead_status(
    *,
    exact_gap_numerator: int,
    remainder_to_coefficient_functional: bool,
) -> str:
    if exact_gap_numerator == 1:
        return "covered_by_gap_one_bridge"
    if remainder_to_coefficient_functional:
        return "empirically_coefficient_functional_frontier"
    return "coefficient_functionality_counterexample_candidate"


def certified_positive_lookahead_state_window_rows(
    max_n: int = 1200,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, object]]:
    """
    Export certified positive-lookahead windows with coefficient diagnostics.

    This surface stays empirical. It helps decide whether the next theorem move
    should extend the current `gap = 1` bridge or search for a sharper
    criterion/counterexample once that regime fails to appear.
    """
    case_rows: list[dict[str, object]] = []
    for n in range(2, max_n + 1):
        try:
            profile = carried_prefix_visibility_profile(
                n,
                base=base,
                n_blocks=n_blocks,
                max_lookahead_blocks=max_lookahead_blocks,
            )
        except ValueError:
            continue
        if profile.q <= 0 or profile.certified_lookahead_blocks <= 0:
            continue
        comparison = carry_remainder_comparison(
            n,
            base=base,
            n_blocks=n_blocks,
            prefer_m=profile.m,
            max_lookahead_blocks=max_lookahead_blocks,
        )
        remainder_to_coefficient_map = comparison.remainder_to_coefficient_map
        theorem_frontier_status = _certified_positive_lookahead_status(
            exact_gap_numerator=profile.exact_gap_numerator,
            remainder_to_coefficient_functional=comparison.coefficient_functional,
        )
        case_rows.append(
            {
                "group": "certified_positive_lookahead_case",
                "n": profile.n,
                "periodic_modulus": profile.periodic_modulus,
                "base": profile.base,
                "m": profile.m,
                "B": profile.B,
                "q": profile.q,
                "k": profile.k,
                "period": profile.period,
                "preperiod_digits": profile.preperiod_digits,
                "requested_blocks": profile.requested_blocks,
                "lookahead_blocks": profile.lookahead_blocks,
                "certified_lookahead_blocks": profile.certified_lookahead_blocks,
                "lookahead_lower_bound": profile.lookahead_lower_bound,
                "exact_gap_numerator": profile.exact_gap_numerator,
                "lookahead_certificate_matches": profile.lookahead_certificate_matches,
                "remainder_to_coefficient_functional": comparison.coefficient_functional,
                "remainder_to_coefficient_fiber_signature": remainder_to_coefficient_map.fiber_signature,
                "remainder_to_carry_functional": comparison.remainder_to_carry_map.is_functional,
                "carry_to_remainder_functional": comparison.carry_to_remainder_map.is_functional,
                "obstruction_class": comparison.decision_report.obstruction_class,
                "theorem_frontier_status": theorem_frontier_status,
                **claim_context_for_parameters(
                    ("small_k_visibility_threshold",),
                    base=profile.base,
                    n=profile.n,
                    requested_blocks=profile.requested_blocks,
                ),
            }
        )
    case_rows.sort(
        key=lambda row: (
            CERTIFIED_POSITIVE_LOOKAHEAD_STATUS_ORDER[str(row["theorem_frontier_status"])],
            int(row["exact_gap_numerator"]),
            int(row["certified_lookahead_blocks"]),
            int(row["k"]),
            int(row["n"]),
        )
    )

    status_counts = {
        status: sum(1 for row in case_rows if row["theorem_frontier_status"] == status)
        for status in CERTIFIED_POSITIVE_LOOKAHEAD_STATUS_ORDER
    }
    next_theorem_direction = (
        "extend_gap_one_bridge"
        if status_counts["covered_by_gap_one_bridge"] > 0
        else "refine_gap_criterion_or_search_counterexample"
    )
    summary_row = {
        "group": "certified_positive_lookahead_summary",
        "base": base,
        "requested_blocks": n_blocks,
        "max_n": max_n,
        "total_rows": len(case_rows),
        "gap_one_covered_rows": status_counts["covered_by_gap_one_bridge"],
        "empirical_coefficient_functional_frontier_rows": status_counts[
            "empirically_coefficient_functional_frontier"
        ],
        "coefficient_functionality_counterexample_candidates": status_counts[
            "coefficient_functionality_counterexample_candidate"
        ],
        "smallest_exact_gap_numerator": (
            min(int(row["exact_gap_numerator"]) for row in case_rows)
            if case_rows
            else None
        ),
        "next_theorem_direction": next_theorem_direction,
    }
    return [summary_row, *case_rows]


def certified_positive_lookahead_coefficient_conflict_rows(
    max_n: int = 1200,
    *,
    base: int = 10,
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, object]]:
    """
    Export the first coefficient-functionality conflicts inside certified windows.

    This is a drill-down beneath `certified_positive_lookahead_state_window_rows`:
    it records concrete obstruction witnesses without promoting the open
    visibility or factorization claims.
    """
    source_rows = certified_positive_lookahead_state_window_rows(
        max_n,
        base=base,
        n_blocks=n_blocks,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    conflict_rows: list[dict[str, object]] = []
    for row in source_rows:
        if row.get("group") != "certified_positive_lookahead_case":
            continue
        if row.get("theorem_frontier_status") != "coefficient_functionality_counterexample_candidate":
            continue
        comparison = carry_remainder_comparison(
            int(row["n"]),
            base=int(row["base"]),
            n_blocks=int(row["requested_blocks"]),
            prefer_m=int(row["m"]),
            max_lookahead_blocks=max_lookahead_blocks,
        )
        conflict = comparison.first_remainder_to_coefficient_conflict
        if conflict is None:
            continue
        conflict_rows.append(
            {
                "group": "coefficient_conflict_witness",
                "n": row["n"],
                "periodic_modulus": row["periodic_modulus"],
                "base": row["base"],
                "m": row["m"],
                "B": row["B"],
                "q": row["q"],
                "k": row["k"],
                "period": row["period"],
                "preperiod_digits": row["preperiod_digits"],
                "requested_blocks": row["requested_blocks"],
                "lookahead_blocks": row["lookahead_blocks"],
                "certified_lookahead_blocks": row["certified_lookahead_blocks"],
                "lookahead_lower_bound": row["lookahead_lower_bound"],
                "exact_gap_numerator": row["exact_gap_numerator"],
                "lookahead_certificate_matches": row["lookahead_certificate_matches"],
                "theorem_frontier_status": row["theorem_frontier_status"],
                "remainder_to_coefficient_fiber_signature": row[
                    "remainder_to_coefficient_fiber_signature"
                ],
                "remainder_to_carry_functional": row["remainder_to_carry_functional"],
                "carry_to_remainder_functional": row["carry_to_remainder_functional"],
                "obstruction_class": row["obstruction_class"],
                "conflict_remainder_state": conflict.remainder_state,
                "conflict_positions": list(conflict.positions),
                "conflict_coefficients": list(conflict.coefficients),
                "conflict_carry_states": list(conflict.carry_states),
                "conflict_block_values": list(conflict.block_values),
                "conflict_output_hidden": conflict.output_hidden,
                "conflict_position_gap": conflict.position_gap,
                "conflict_coefficient_delta": conflict.coefficient_delta,
                "related_claim_ids": row.get("related_claim_ids", []),
                "related_open_claim_ids": row.get("related_open_claim_ids", []),
                "matching_claim_ids": row.get("matching_claim_ids", []),
                "matching_witness_ids": row.get("matching_witness_ids", []),
            }
        )
    conflict_rows.sort(
        key=lambda row: (
            int(row["exact_gap_numerator"]),
            int(row["certified_lookahead_blocks"]),
            int(row["k"]),
            int(row["n"]),
            int(row["conflict_positions"][0]),
            int(row["conflict_remainder_state"]),
        )
    )
    selected_rows = conflict_rows if top <= 0 else conflict_rows[:top]
    summary_row = {
        "group": "coefficient_conflict_summary",
        "base": base,
        "requested_blocks": n_blocks,
        "max_n": max_n,
        "total_conflict_rows": len(conflict_rows),
        "emitted_conflict_rows": len(selected_rows),
        "output_hidden_conflict_rows": sum(
            1 for row in conflict_rows if bool(row["conflict_output_hidden"])
        ),
        "smallest_exact_gap_numerator": (
            int(conflict_rows[0]["exact_gap_numerator"]) if conflict_rows else None
        ),
        "first_conflict_n": int(conflict_rows[0]["n"]) if conflict_rows else None,
        "first_conflict_tuple": (
            [
                int(conflict_rows[0]["base"]),
                int(conflict_rows[0]["n"]),
                int(conflict_rows[0]["m"]),
                int(conflict_rows[0]["B"]),
                int(conflict_rows[0]["q"]),
                int(conflict_rows[0]["k"]),
                int(conflict_rows[0]["certified_lookahead_blocks"]),
                int(conflict_rows[0]["exact_gap_numerator"]),
            ]
            if conflict_rows
            else None
        ),
    }
    return [summary_row, *selected_rows]


def certified_positive_lookahead_coefficient_conflict_atlas_rows(
    max_n: int = 1200,
    *,
    bases: tuple[int, ...] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, object]]:
    """
    Export a cross-base atlas of certified positive-lookahead conflicts.

    This composes the single-base conflict drill-down without promoting the
    observed obstruction patterns into new atlas claims. Rows remain empirical
    support beneath the open visibility/factorization boundary.
    """
    base_summaries: list[dict[str, object]] = []
    atlas_rows: list[dict[str, object]] = []
    for base in bases:
        base_rows = certified_positive_lookahead_coefficient_conflict_rows(
            max_n,
            base=base,
            n_blocks=n_blocks,
            top=0,
            max_lookahead_blocks=max_lookahead_blocks,
        )
        base_summary = dict(base_rows[0])
        base_summaries.append(base_summary)
        conflict_rows = [
            row for row in base_rows if row.get("group") == "coefficient_conflict_witness"
        ]
        for base_rank, row in enumerate(conflict_rows, start=1):
            atlas_rows.append(
                {
                    **row,
                    "group": "coefficient_conflict_atlas_case",
                    "base_conflict_rank": base_rank,
                    "base_total_conflict_rows": base_summary["total_conflict_rows"],
                    "base_output_hidden_conflict_rows": base_summary[
                        "output_hidden_conflict_rows"
                    ],
                    "base_smallest_exact_gap_numerator": base_summary[
                        "smallest_exact_gap_numerator"
                    ],
                }
            )

    atlas_rows.sort(
        key=lambda row: (
            int(row["exact_gap_numerator"]),
            int(row["certified_lookahead_blocks"]),
            int(row["k"]),
            int(row["n"]),
            int(row["conflict_positions"][0]),
            int(row["conflict_remainder_state"]),
        )
    )
    selected_rows = atlas_rows if top <= 0 else atlas_rows[:top]
    for global_rank, row in enumerate(selected_rows, start=1):
        row["global_conflict_rank"] = global_rank

    first_base10_row = next(
        (
            row
            for row in atlas_rows
            if int(row["base"]) == 10 and int(row["base_conflict_rank"]) == 1
        ),
        None,
    )
    summary_row = {
        "group": "coefficient_conflict_atlas_summary",
        "bases": list(bases),
        "requested_blocks": n_blocks,
        "max_n": max_n,
        "total_conflict_rows": sum(
            int(summary["total_conflict_rows"]) for summary in base_summaries
        ),
        "emitted_conflict_rows": len(selected_rows),
        "base_count": len(bases),
        "bases_with_conflicts": sum(
            1 for summary in base_summaries if int(summary["total_conflict_rows"]) > 0
        ),
        "output_hidden_conflict_rows": sum(
            int(summary["output_hidden_conflict_rows"]) for summary in base_summaries
        ),
        "smallest_exact_gap_numerator": (
            int(atlas_rows[0]["exact_gap_numerator"]) if atlas_rows else None
        ),
        "first_conflict_tuple": (
            [
                int(atlas_rows[0]["base"]),
                int(atlas_rows[0]["n"]),
                int(atlas_rows[0]["m"]),
                int(atlas_rows[0]["B"]),
                int(atlas_rows[0]["q"]),
                int(atlas_rows[0]["k"]),
                int(atlas_rows[0]["certified_lookahead_blocks"]),
                int(atlas_rows[0]["exact_gap_numerator"]),
            ]
            if atlas_rows
            else None
        ),
        "first_base10_conflict_tuple": (
            [
                int(first_base10_row["base"]),
                int(first_base10_row["n"]),
                int(first_base10_row["m"]),
                int(first_base10_row["B"]),
                int(first_base10_row["q"]),
                int(first_base10_row["k"]),
                int(first_base10_row["certified_lookahead_blocks"]),
                int(first_base10_row["exact_gap_numerator"]),
            ]
            if first_base10_row
            else None
        ),
        "base_summaries": [
            {
                "base": int(summary["base"]),
                "total_conflict_rows": int(summary["total_conflict_rows"]),
                "output_hidden_conflict_rows": int(summary["output_hidden_conflict_rows"]),
                "smallest_exact_gap_numerator": summary["smallest_exact_gap_numerator"],
                "first_conflict_n": summary["first_conflict_n"],
                "first_conflict_tuple": summary["first_conflict_tuple"],
            }
            for summary in base_summaries
        ],
    }
    return [summary_row, *selected_rows]


def _coefficient_conflict_shape_key(row: dict[str, object]) -> tuple[object, ...]:
    return (
        int(row["periodic_modulus"]),
        int(row["k"]),
        int(row["conflict_remainder_state"]),
        tuple(int(position) for position in row["conflict_positions"]),
        tuple(int(carry_state) for carry_state in row["conflict_carry_states"]),
        bool(row["conflict_output_hidden"]),
    )


def _coefficient_conflict_shape_signature(shape_key: tuple[object, ...]) -> str:
    periodic_modulus, k, remainder_state, positions, carry_states, output_hidden = shape_key
    return (
        f"periodic_modulus={periodic_modulus};"
        f"k={k};"
        f"remainder_state={remainder_state};"
        f"positions={list(positions)};"
        f"carry_states={list(carry_states)};"
        f"output_hidden={str(output_hidden).lower()}"
    )


def _coefficient_conflict_member_tuple(row: dict[str, object]) -> list[int]:
    return [
        int(row["base"]),
        int(row["n"]),
        int(row["m"]),
        int(row["B"]),
        int(row["q"]),
        int(row["k"]),
        int(row["certified_lookahead_blocks"]),
        int(row["exact_gap_numerator"]),
    ]


def certified_positive_lookahead_coefficient_conflict_family_rows(
    max_n: int = 1200,
    *,
    bases: tuple[int, ...] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, object]]:
    """
    Mine recurring hidden-output coefficient-conflict shapes across bases.

    The grouping is deliberately empirical and finite-window-only. It preserves
    the exact remainder `k`, stripped periodic modulus, conflict remainder
    state, conflict positions, incoming carry states, and hidden-output flag
    while allowing the block value and quotient `q` to vary across instruments.
    """
    atlas_rows = certified_positive_lookahead_coefficient_conflict_atlas_rows(
        max_n,
        bases=bases,
        n_blocks=n_blocks,
        top=0,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    hidden_conflict_rows = [
        row
        for row in atlas_rows
        if row.get("group") == "coefficient_conflict_atlas_case"
        and bool(row["conflict_output_hidden"])
    ]

    grouped_rows: dict[tuple[object, ...], list[dict[str, object]]] = {}
    for row in hidden_conflict_rows:
        grouped_rows.setdefault(_coefficient_conflict_shape_key(row), []).append(row)

    family_rows: list[dict[str, object]] = []
    for shape_key, members in grouped_rows.items():
        if len(members) <= 1:
            continue
        members.sort(
            key=lambda row: (
                int(row["base"]),
                int(row["n"]),
                int(row["exact_gap_numerator"]),
            )
        )
        periodic_modulus, k, remainder_state, positions, carry_states, output_hidden = shape_key
        member_bases = sorted({int(row["base"]) for row in members})
        member_ns = sorted({int(row["n"]) for row in members})
        member_periods = sorted({int(row["period"]) for row in members})
        min_gap = min(int(row["exact_gap_numerator"]) for row in members)
        min_lookahead = min(int(row["certified_lookahead_blocks"]) for row in members)
        contains_base10_68 = any(int(row["base"]) == 10 and int(row["n"]) == 68 for row in members)
        if contains_base10_68 and len(member_bases) > 1:
            theorem_candidate_kind = "composite68_cross_base_family_candidate"
            next_lean_theorem_recommendation = "classify_composite68_cross_base_hidden_output_conflict"
        elif len(member_bases) > 1:
            theorem_candidate_kind = "cross_base_hidden_output_family_candidate"
            next_lean_theorem_recommendation = "classify_hidden_output_conflict_shape_family"
        else:
            theorem_candidate_kind = "same_base_hidden_output_family_candidate"
            next_lean_theorem_recommendation = "add_next_finite_example_package"

        family_rows.append(
            {
                "group": "coefficient_conflict_family",
                "shape_signature": _coefficient_conflict_shape_signature(shape_key),
                "shape_periodic_modulus": periodic_modulus,
                "shape_k": k,
                "shape_conflict_remainder_state": remainder_state,
                "shape_conflict_positions": list(positions),
                "shape_conflict_carry_states": list(carry_states),
                "shape_conflict_output_hidden": output_hidden,
                "family_size": len(members),
                "base_count": len(member_bases),
                "bases": member_bases,
                "n_values": member_ns,
                "periods": member_periods,
                "min_exact_gap_numerator": min_gap,
                "min_certified_lookahead_blocks": min_lookahead,
                "min_n": min(member_ns),
                "contains_base10_68": contains_base10_68,
                "theorem_candidate_kind": theorem_candidate_kind,
                "next_lean_theorem_recommendation": next_lean_theorem_recommendation,
                "member_tuples": [_coefficient_conflict_member_tuple(row) for row in members],
                "members": [
                    {
                        "base": int(row["base"]),
                        "n": int(row["n"]),
                        "m": int(row["m"]),
                        "B": int(row["B"]),
                        "q": int(row["q"]),
                        "k": int(row["k"]),
                        "period": int(row["period"]),
                        "preperiod_digits": int(row["preperiod_digits"]),
                        "certified_lookahead_blocks": int(row["certified_lookahead_blocks"]),
                        "exact_gap_numerator": int(row["exact_gap_numerator"]),
                        "conflict_coefficients": list(row["conflict_coefficients"]),
                        "conflict_block_values": list(row["conflict_block_values"]),
                    }
                    for row in members
                ],
            }
        )

    family_rows.sort(
        key=lambda row: (
            -int(row["base_count"]),
            -int(row["family_size"]),
            int(row["min_exact_gap_numerator"]),
            int(row["min_certified_lookahead_blocks"]),
            int(row["shape_k"]),
            int(row["min_n"]),
            str(row["shape_signature"]),
        )
    )
    for family_rank, row in enumerate(family_rows, start=1):
        row["family_rank"] = family_rank

    selected_rows = family_rows if top <= 0 else family_rows[:top]
    recommended_family = next(
        (
            row
            for row in family_rows
            if bool(row["contains_base10_68"]) and int(row["base_count"]) > 1
        ),
        None,
    )
    if recommended_family is None:
        recommended_family = next(
            (row for row in family_rows if int(row["base_count"]) > 1),
            None,
        )
    if recommended_family is None:
        recommended_family = family_rows[0] if family_rows else None

    if recommended_family is None:
        next_lean_theorem_recommendation = "mine_wider_bounds_before_lean_family_theorem"
        recommendation_reason = "no repeated hidden-output coefficient-conflict shape appeared at the selected bound"
    else:
        next_lean_theorem_recommendation = str(
            recommended_family["next_lean_theorem_recommendation"]
        )
        if bool(recommended_family["contains_base10_68"]) and int(recommended_family["base_count"]) > 1:
            recommendation_reason = (
                "the Composite68 obstruction already has a Lean finite package and "
                "recurs across base instruments with the same hidden-output conflict shape"
            )
        elif int(recommended_family["base_count"]) > 1:
            recommendation_reason = (
                "a cross-base hidden-output conflict family appeared before a Lean-backed "
                "Composite68 family was available at this bound"
            )
        else:
            recommendation_reason = (
                "only same-base repeated shapes appeared, so another finite package is safer "
                "than a family-level classification"
            )

    summary_row = {
        "group": "coefficient_conflict_family_summary",
        "bases": list(bases),
        "requested_blocks": n_blocks,
        "max_n": max_n,
        "total_hidden_conflict_rows": len(hidden_conflict_rows),
        "total_shape_groups": len(grouped_rows),
        "repeated_shape_families": len(family_rows),
        "emitted_family_rows": len(selected_rows),
        "cross_base_shape_families": sum(
            1 for row in family_rows if int(row["base_count"]) > 1
        ),
        "largest_base_count": (
            max(int(row["base_count"]) for row in family_rows) if family_rows else 0
        ),
        "largest_family_size": (
            max(int(row["family_size"]) for row in family_rows) if family_rows else 0
        ),
        "strongest_family_signature": (
            family_rows[0]["shape_signature"] if family_rows else None
        ),
        "composite68_cross_base_family_present": (
            any(
                bool(row["contains_base10_68"]) and int(row["base_count"]) > 1
                for row in family_rows
            )
        ),
        "recommended_family_signature": (
            recommended_family["shape_signature"] if recommended_family else None
        ),
        "recommended_family_member_tuples": (
            recommended_family["member_tuples"] if recommended_family else []
        ),
        "next_lean_theorem_recommendation": next_lean_theorem_recommendation,
        "recommendation_reason": recommendation_reason,
    }
    return [summary_row, *selected_rows]


COMPOSITE68_HIDDEN_OUTPUT_SHAPE_KEY: tuple[object, ...] = (
    17,
    4,
    4,
    (1, 5),
    (0, 60),
    True,
)


def _composite68_shape_role(*, base: int, shape_matches: bool) -> str:
    if not shape_matches:
        return "other_composite68_conflict_shape"
    if base == 10:
        return "lean_packaged_base10_anchor"
    if base == 30:
        return "next_base30_package_candidate"
    return "additional_cross_base_family_signal"


def composite68_cross_base_obstruction_sweep_rows(
    max_base: int = 120,
    *,
    n_blocks: int = 8,
    top: int = 20,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, object]]:
    """
    Sweep base instruments for the `N = 68` hidden-output conflict shape.

    This is an empirical selector for the next Lean package. It keeps the
    finite obstruction local to `Composite68` and does not promote the open
    visibility or factorization claims.
    """
    case_rows: list[dict[str, object]] = []
    for base in range(2, max_base + 1):
        try:
            profile = carried_prefix_visibility_profile(
                68,
                base=base,
                n_blocks=n_blocks,
                max_lookahead_blocks=max_lookahead_blocks,
            )
        except ValueError:
            continue
        if profile.q <= 0 or profile.certified_lookahead_blocks <= 0:
            continue
        comparison = carry_remainder_comparison(
            profile.n,
            base=profile.base,
            n_blocks=profile.requested_blocks,
            prefer_m=profile.m,
            max_lookahead_blocks=max_lookahead_blocks,
        )
        conflict = comparison.first_remainder_to_coefficient_conflict
        if conflict is None:
            continue
        shape_key = (
            profile.periodic_modulus,
            profile.k,
            conflict.remainder_state,
            conflict.positions,
            conflict.carry_states,
            conflict.output_hidden,
        )
        shape_matches = shape_key == COMPOSITE68_HIDDEN_OUTPUT_SHAPE_KEY
        block_base_mod_n = profile.B % profile.n
        case_rows.append(
            {
                "group": "composite68_cross_base_sweep_case",
                "n": profile.n,
                "periodic_modulus": profile.periodic_modulus,
                "base": profile.base,
                "m": profile.m,
                "B": profile.B,
                "q": profile.q,
                "k": profile.k,
                "period": profile.period,
                "preperiod_digits": profile.preperiod_digits,
                "requested_blocks": profile.requested_blocks,
                "lookahead_blocks": profile.lookahead_blocks,
                "certified_lookahead_blocks": profile.certified_lookahead_blocks,
                "lookahead_lower_bound": profile.lookahead_lower_bound,
                "exact_gap_numerator": profile.exact_gap_numerator,
                "lookahead_certificate_matches": profile.lookahead_certificate_matches,
                "conflict_remainder_state": conflict.remainder_state,
                "conflict_positions": list(conflict.positions),
                "conflict_coefficients": list(conflict.coefficients),
                "conflict_carry_states": list(conflict.carry_states),
                "conflict_block_values": list(conflict.block_values),
                "conflict_output_hidden": conflict.output_hidden,
                "conflict_position_gap": conflict.position_gap,
                "conflict_coefficient_delta": conflict.coefficient_delta,
                "shape_signature": _coefficient_conflict_shape_signature(shape_key),
                "composite68_hidden_output_shape_match": shape_matches,
                "selected_block_base_mod_68": block_base_mod_n,
                "selected_block_base_congruent_to_4_mod_68": block_base_mod_n == 4,
                "lean_package_role": _composite68_shape_role(
                    base=profile.base,
                    shape_matches=shape_matches,
                ),
            }
        )

    case_rows.sort(
        key=lambda row: (
            not bool(row["composite68_hidden_output_shape_match"]),
            int(row["base"]),
            int(row["exact_gap_numerator"]),
        )
    )
    selected_rows = case_rows if top <= 0 else case_rows[:top]
    target_rows = [
        row for row in case_rows if bool(row["composite68_hidden_output_shape_match"])
    ]
    base10_row = next((row for row in target_rows if int(row["base"]) == 10), None)
    base30_row = next((row for row in target_rows if int(row["base"]) == 30), None)
    if base30_row is not None and len(target_rows) > 1:
        recommended_next_lean_task = "add_composite68_base30_finite_package_then_cross_base_shape_lemma"
        recommendation_reason = (
            "the base-10 Lean anchor recurs in base 30 and additional base instruments "
            "with the same hidden-output shape, so package base 30 next before "
            "attempting the generic shape lemma"
        )
    elif len(target_rows) > 1:
        recommended_next_lean_task = "add_next_composite68_shape_member_package"
        recommendation_reason = (
            "the base-10 Lean anchor has a repeated hidden-output shape, but base 30 "
            "is not present at this bound"
        )
    else:
        recommended_next_lean_task = "mine_wider_composite68_base_bounds_before_family_lean"
        recommendation_reason = (
            "the exact Composite68 hidden-output shape has not yet recurred at this bound"
        )

    summary_row = {
        "group": "composite68_cross_base_sweep_summary",
        "n": 68,
        "requested_blocks": n_blocks,
        "max_base": max_base,
        "total_bases_scanned": max(max_base - 1, 0),
        "total_conflict_rows": len(case_rows),
        "emitted_case_rows": len(selected_rows),
        "target_shape_signature": _coefficient_conflict_shape_signature(
            COMPOSITE68_HIDDEN_OUTPUT_SHAPE_KEY
        ),
        "target_shape_rows": len(target_rows),
        "target_shape_bases": [int(row["base"]) for row in target_rows],
        "target_shape_member_tuples": [
            _coefficient_conflict_member_tuple(row) for row in target_rows
        ],
        "base10_anchor_tuple": (
            _coefficient_conflict_member_tuple(base10_row) if base10_row else None
        ),
        "base30_package_candidate_tuple": (
            _coefficient_conflict_member_tuple(base30_row) if base30_row else None
        ),
        "base30_target_present": base30_row is not None,
        "all_target_rows_have_B_mod_68_eq_4": all(
            bool(row["selected_block_base_congruent_to_4_mod_68"])
            for row in target_rows
        ),
        "recommended_next_lean_task": recommended_next_lean_task,
        "recommendation_reason": recommendation_reason,
    }
    return [summary_row, *selected_rows]


def composite68_congruence_family_rows(
    max_base: int = 120,
    *,
    max_m: int = 8,
    n_blocks: int = 8,
    top: int = 0,
    max_lookahead_blocks: int = 128,
) -> list[dict[str, object]]:
    """
    Enumerate bounded `N = 68` coordinates with `B = base^m ≡ 4 (mod 68)`.

    The Lean obstruction now covers every good finite window in this congruence
    family once positions `1` and `5` are present. The hidden-output conflict
    shape remains an empirical classifier on top of that exact finite theorem.
    """
    case_rows: list[dict[str, object]] = []
    for base in range(2, max_base + 1):
        for m in range(1, max_m + 1):
            B = pow(base, m)
            if B <= 68 or B % 68 != 4:
                continue
            try:
                profile = carried_prefix_visibility_profile(
                    68,
                    base=base,
                    n_blocks=n_blocks,
                    prefer_m=m,
                    max_lookahead_blocks=max_lookahead_blocks,
                )
            except ValueError:
                continue

            conflict = None
            try:
                comparison = carry_remainder_comparison(
                    profile.n,
                    base=profile.base,
                    n_blocks=profile.requested_blocks,
                    prefer_m=profile.m,
                    max_lookahead_blocks=max_lookahead_blocks,
                )
                conflict = comparison.first_remainder_to_coefficient_conflict
            except ValueError:
                conflict = None

            shape_key: tuple[object, ...] | None = None
            if conflict is not None:
                shape_key = (
                    profile.periodic_modulus,
                    profile.k,
                    conflict.remainder_state,
                    conflict.positions,
                    conflict.carry_states,
                    conflict.output_hidden,
                )
            shape_matches = shape_key == COMPOSITE68_HIDDEN_OUTPUT_SHAPE_KEY
            positions_available = n_blocks >= 6
            case_rows.append(
                {
                    "group": "composite68_congruence_family_case",
                    "n": profile.n,
                    "periodic_modulus": profile.periodic_modulus,
                    "base": profile.base,
                    "m": profile.m,
                    "B": profile.B,
                    "q": profile.q,
                    "k": profile.k,
                    "period": profile.period,
                    "preperiod_digits": profile.preperiod_digits,
                    "requested_blocks": profile.requested_blocks,
                    "lookahead_blocks": profile.lookahead_blocks,
                    "certified_lookahead_blocks": profile.certified_lookahead_blocks,
                    "lookahead_lower_bound": profile.lookahead_lower_bound,
                    "exact_gap_numerator": profile.exact_gap_numerator,
                    "lookahead_certificate_matches": profile.lookahead_certificate_matches,
                    "selected_block_base_mod_68": profile.B % 68,
                    "selected_block_base_congruent_to_4_mod_68": profile.B % 68 == 4,
                    "finite_window_positions_available": positions_available,
                    "lean_obstruction_covered": positions_available,
                    "lean_obstruction_theorem": (
                        "BlockCoordinate.not_coefficientFunctional_one_five_of_modulus_eq_"
                        "sixty_eight_and_blockBase_mod_eq_four"
                    ),
                    "conflict_remainder_state": (
                        conflict.remainder_state if conflict is not None else None
                    ),
                    "conflict_positions": (
                        list(conflict.positions) if conflict is not None else []
                    ),
                    "conflict_coefficients": (
                        list(conflict.coefficients) if conflict is not None else []
                    ),
                    "conflict_carry_states": (
                        list(conflict.carry_states) if conflict is not None else []
                    ),
                    "conflict_block_values": (
                        list(conflict.block_values) if conflict is not None else []
                    ),
                    "conflict_output_hidden": (
                        conflict.output_hidden if conflict is not None else None
                    ),
                    "conflict_position_gap": (
                        conflict.position_gap if conflict is not None else None
                    ),
                    "conflict_coefficient_delta": (
                        conflict.coefficient_delta if conflict is not None else None
                    ),
                    "shape_signature": (
                        _coefficient_conflict_shape_signature(shape_key)
                        if shape_key is not None
                        else None
                    ),
                    "composite68_hidden_output_shape_match": shape_matches,
                    "empirical_classifier_status": (
                        "certified_hidden_output_shape_match"
                        if shape_matches
                        else "congruence_family_member"
                    ),
                }
            )

    case_rows.sort(
        key=lambda row: (
            not bool(row["composite68_hidden_output_shape_match"]),
            int(row["certified_lookahead_blocks"]),
            int(row["exact_gap_numerator"]),
            int(row["base"]),
            int(row["m"]),
        )
    )
    selected_rows = case_rows if top <= 0 else case_rows[:top]
    target_rows = [
        row for row in case_rows if bool(row["composite68_hidden_output_shape_match"])
    ]
    summary_row = {
        "group": "composite68_congruence_family_summary",
        "n": 68,
        "requested_blocks": n_blocks,
        "max_base": max_base,
        "max_m": max_m,
        "total_congruence_rows": len(case_rows),
        "emitted_case_rows": len(selected_rows),
        "lean_obstruction_covered_rows": sum(
            1 for row in case_rows if bool(row["lean_obstruction_covered"])
        ),
        "target_shape_signature": _coefficient_conflict_shape_signature(
            COMPOSITE68_HIDDEN_OUTPUT_SHAPE_KEY
        ),
        "hidden_output_shape_rows": len(target_rows),
        "hidden_output_shape_bases": sorted({int(row["base"]) for row in target_rows}),
        "hidden_output_shape_member_tuples": [
            _coefficient_conflict_member_tuple(row) for row in target_rows
        ],
        "all_congruence_rows_have_k_eq_4": all(int(row["k"]) == 4 for row in case_rows),
        "all_congruence_rows_have_B_mod_68_eq_4": all(
            int(row["selected_block_base_mod_68"]) == 4 for row in case_rows
        ),
        "lean_obstruction_theorem": (
            "BlockCoordinate.not_coefficientFunctional_one_five_of_modulus_eq_"
            "sixty_eight_and_blockBase_mod_eq_four"
        ),
        "classifier_status": (
            "empirical_hidden_output_shape_classifier_beneath_finite_lean_obstruction"
        ),
    }
    return [summary_row, *selected_rows]


def incoming_carry_counterexample_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    kmax: int = 6,
    mmax: int = 12,
) -> list[dict[str, object]]:
    """Rows where incoming carry appears before the local overflow boundary."""
    return [
        row
        for row in visibility_profile_rows(
            max_n,
            base=base,
            n_blocks=n_blocks,
            kmax=kmax,
            mmax=mmax,
        )
        if row["first_incoming_carry_position"] is not None
        and (
            row["first_local_overflow_position"] is None
            or int(row["first_incoming_carry_position"]) < int(row["first_local_overflow_position"])
        )
    ]


def same_core_visibility_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_block_base: int = 100_000,
    max_m: int = 12,
    require_interval_law: bool = True,
) -> list[dict[str, object]]:
    """Export same-core family comparisons for one base."""
    rows: list[dict[str, object]] = []
    for n in range(2, max_n + 1):
        try:
            prefer_m = select_same_core_prefer_m(
                n,
                base=base,
                n_blocks=n_blocks,
                max_m=max_m,
                max_block_base=max_block_base,
                require_interval_law=require_interval_law,
            )
            if prefer_m is None:
                continue
            comparison = same_core_visibility_comparison(
                n,
                base=base,
                n_blocks=n_blocks,
                prefer_m=prefer_m,
            )
        except Exception:
            continue
        if comparison.actual_profile.n == comparison.core_profile.n:
            continue
        if comparison.actual_profile.B > max_block_base:
            continue
        if comparison.actual_profile.k <= 1:
            continue
        if require_interval_law and not comparison.interval_family_law_holds:
            continue
        rows.append(
            {
                "base": base,
                "actual_n": comparison.actual_profile.n,
                "core_n": comparison.core_profile.n,
                "m": comparison.actual_profile.m,
                "B": comparison.actual_profile.B,
                "k": comparison.actual_profile.k,
                "q_actual": comparison.actual_profile.q,
                "q_core": comparison.core_profile.q,
                "q_ratio": comparison.q_ratio,
                "q_ratio_floor_log_k": comparison.q_ratio_floor_log_k,
                "q_ratio_k_exponent": comparison.q_ratio_k_exponent,
                "shift_interval": comparison.shift_interval,
                "incoming_carry_shift": comparison.incoming_carry_shift,
                "local_overflow_shift": comparison.local_overflow_shift,
                "raw_prefix_shift": comparison.raw_prefix_shift,
                "lookahead_shift": comparison.lookahead_shift,
                "interval_family_law_holds": comparison.interval_family_law_holds,
                "exact_shift_law_holds": comparison.exact_shift_law_holds,
                "threshold_shift_endpoint": comparison.threshold_shift_endpoint,
                "family_law": "exact" if comparison.exact_shift_law_holds else "interval",
                **claim_context_for_parameters(
                    (
                        "same_core_threshold_shift_interval",
                        "small_k_visibility_threshold",
                    ),
                    base=base,
                    actual=comparison.actual_profile.n,
                    core=comparison.core_profile.n,
                    requested_blocks=comparison.actual_profile.requested_blocks,
                ),
            }
        )
    rows.sort(
        key=lambda row: (
            row["family_law"] != "exact",
            int(row["k"]),
            int(row["m"]),
            int(row["actual_n"]),
        )
    )
    return rows


VISIBILITY_OPTICS_CANONICAL_ANCHORS = {
    21: 6,
    97: 2,
    249: 3,
    996: 3,
}
VISIBILITY_OPTICS_OPEN_BOUNDARY = (
    "small_k_visibility_threshold",
    "carry_dfa_factorization",
)


def _is_early_carry_intrusion(row: dict[str, object]) -> bool:
    incoming = row.get("first_incoming_carry_position")
    overflow = row.get("first_local_overflow_position")
    if incoming is None:
        return False
    return overflow is None or int(incoming) < int(overflow)


def _visibility_signal_class(
    *,
    row: dict[str, object],
    state_row: dict[str, object] | None,
) -> str | None:
    obstruction = None if state_row is None else str(state_row["obstruction_class"])
    if obstruction == "hidden_graph_obstruction":
        return "hidden_graph_obstruction"
    if obstruction == "visible_preimage_compression":
        return "visible_state_compression"
    if int(row["raw_prefix_agreement_length"]) >= int(row["requested_blocks"]):
        return "transparent_window"
    if _is_early_carry_intrusion(row):
        return "early_carry_intrusion"
    return None


def _profile_to_visibility_row(profile: VisibilityProfile) -> dict[str, object]:
    return {
        "n": profile.n,
        "periodic_modulus": profile.periodic_modulus,
        "base": profile.base,
        "m": profile.m,
        "B": profile.B,
        "q": profile.q,
        "k": profile.k,
        "period": profile.period,
        "preperiod_digits": profile.preperiod_digits,
        "requested_blocks": profile.requested_blocks,
        "lookahead_lower_bound": profile.lookahead_lower_bound,
        "raw_prefix_agreement_length": profile.raw_prefix_agreement_length,
        "predicted_raw_prefix_agreement_length": profile.predicted_raw_prefix_agreement_length,
        "first_local_overflow_position": profile.first_local_overflow_position,
        "first_incoming_carry_position": profile.first_incoming_carry_position,
        "predicted_first_incoming_carry_position": profile.predicted_first_incoming_carry_position,
        "lookahead_blocks": profile.lookahead_blocks,
        "certified_lookahead_blocks": profile.certified_lookahead_blocks,
        "exact_gap_numerator": profile.exact_gap_numerator,
        "mismatch_regime": profile.mismatch_regime,
        "incoming_carry_formula_holds": profile.incoming_carry_formula_holds,
        "agreement_identity_holds": profile.agreement_identity_holds,
        "lookahead_certificate_matches": profile.lookahead_certificate_matches,
        **claim_context_for_parameters(
            (
                "incoming_carry_position_formula",
                "small_k_visibility_threshold",
                "small_k_visibility_heuristic",
            ),
            base=profile.base,
            n=profile.n,
            requested_blocks=profile.requested_blocks,
        ),
    }


def _open_claim_ids(*rows: dict[str, object] | None) -> list[str]:
    ids: list[str] = []
    for claim_id in VISIBILITY_OPTICS_OPEN_BOUNDARY:
        ids.append(claim_id)
    for row in rows:
        if row is None:
            continue
        for claim_id in row.get("related_open_claim_ids", ()):
            if str(claim_id) not in ids:
                ids.append(str(claim_id))
    return ids


def _visibility_optics_score(
    *,
    row: dict[str, object],
    state_row: dict[str, object] | None,
    signal_class: str,
    is_canonical_anchor: bool,
) -> tuple[int, list[str]]:
    score = 0
    reasons: list[str] = []
    requested_blocks = int(row["requested_blocks"])
    raw_agreement = int(row["raw_prefix_agreement_length"])
    hidden_gap = max(requested_blocks - raw_agreement, 0)

    if is_canonical_anchor:
        score += 100
        reasons.append("canonical anchor")
    if signal_class == "transparent_window":
        score += 35
        reasons.append("raw prefix stays visible across the requested window")
    if signal_class == "early_carry_intrusion":
        score += 55
        reasons.append("incoming carry arrives before local overflow")
    if signal_class == "visible_state_compression":
        score += 70
        reasons.append("state map has visible preimage compression")
    if signal_class == "hidden_graph_obstruction":
        score += 80
        reasons.append("state graph obstruction is hidden from visible output")
    if hidden_gap > 0:
        score += hidden_gap * 6
        reasons.append(f"{hidden_gap} requested block(s) are not raw-visible")
    if int(row["certified_lookahead_blocks"]) > int(row["lookahead_lower_bound"]):
        score += 10
        reasons.append("certified lookahead exceeds the tail-mass lower bound")

    if state_row is not None:
        forward_profile = state_row.get("forward_profile", {})
        reverse_profile = state_row.get("reverse_profile", {})
        forward_preimages = int(forward_profile.get("max_preimage_size", 1))
        reverse_preimages = int(reverse_profile.get("max_preimage_size", 1))
        compression = max(forward_preimages, reverse_preimages)
        if compression > 1:
            score += compression * 8
            reasons.append(f"state-map compression has max preimage size {compression}")
        state_gap = abs(int(state_row.get("graph_state_gap", 0)))
        if state_gap:
            score += min(state_gap, 8) * 3
            reasons.append(f"carry/remainder state-count gap is {state_gap}")

    score += 15
    reasons.append("touches an open visibility/factorization boundary")
    return score, reasons


def _visibility_optics_case_row(
    *,
    visibility_row: dict[str, object],
    state_row: dict[str, object] | None,
    is_canonical_anchor: bool,
    group: str,
) -> dict[str, object] | None:
    signal_class = _visibility_signal_class(row=visibility_row, state_row=state_row)
    if signal_class is None:
        return None
    score, score_reasons = _visibility_optics_score(
        row=visibility_row,
        state_row=state_row,
        signal_class=signal_class,
        is_canonical_anchor=is_canonical_anchor,
    )
    row = {
        "group": group,
        "n": visibility_row["n"],
        "periodic_modulus": visibility_row["periodic_modulus"],
        "base": visibility_row["base"],
        "m": visibility_row["m"],
        "B": visibility_row["B"],
        "q": visibility_row["q"],
        "k": visibility_row["k"],
        "period": visibility_row["period"],
        "preperiod_digits": visibility_row["preperiod_digits"],
        "raw_prefix_agreement_length": visibility_row["raw_prefix_agreement_length"],
        "first_incoming_carry_position": visibility_row["first_incoming_carry_position"],
        "first_local_overflow_position": visibility_row["first_local_overflow_position"],
        "lookahead_lower_bound": visibility_row["lookahead_lower_bound"],
        "certified_lookahead_blocks": visibility_row["certified_lookahead_blocks"],
        "mismatch_regime": visibility_row["mismatch_regime"],
        "factorization_regime": None,
        "obstruction_class": None,
        "carry_state_count": None,
        "remainder_state_count": None,
        "forward_preimage_signature": None,
        "reverse_ambiguity_signature": None,
        "visibility_signal_score": score,
        "signal_class": signal_class,
        "score_reasons": score_reasons,
        "why_interesting": "; ".join(score_reasons),
        "related_open_claim_ids": _open_claim_ids(visibility_row, state_row),
    }
    if state_row is not None:
        row.update(
            {
                "factorization_regime": state_row["factorization_regime"],
                "obstruction_class": state_row["obstruction_class"],
                "carry_state_count": state_row["carry_state_count"],
                "remainder_state_count": state_row["remainder_state_count"],
                "forward_preimage_signature": state_row["forward_preimage_signature"],
                "reverse_ambiguity_signature": state_row["reverse_ambiguity_signature"],
            }
        )
    return row


def _same_core_optics_rows(
    *,
    max_n: int,
    base: int,
    n_blocks: int,
    top: int,
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    visibility_rows = same_core_visibility_rows(
        max_n,
        base=base,
        n_blocks=n_blocks,
    )
    phase_rows = same_core_obstruction_phase_rows(
        max_n,
        base=base,
        n_blocks=n_blocks,
        max_m=8,
    )

    for row in visibility_rows[: max(top, 4)]:
        score = 70 if row["family_law"] == "exact" else 60
        if row["threshold_shift_endpoint"] in {"lower", "upper"}:
            score += 10
        rows.append(
            {
                "group": "same_core_signal",
                "source_surface": "same_core_visibility",
                "signal_class": "same_core_drift",
                "visibility_signal_score": score,
                "base": row["base"],
                "actual_n": row["actual_n"],
                "core_n": row["core_n"],
                "members": [row["core_n"], row["actual_n"]],
                "m": row["m"],
                "B": row["B"],
                "k": row["k"],
                "family_law": row["family_law"],
                "threshold_shift_endpoint": row["threshold_shift_endpoint"],
                "incoming_carry_shift": row["incoming_carry_shift"],
                "local_overflow_shift": row["local_overflow_shift"],
                "raw_prefix_shift": row["raw_prefix_shift"],
                "lookahead_shift": row["lookahead_shift"],
                "score_reasons": [
                    f"same-core {row['family_law']} threshold-shift behavior",
                    "compares actual denominator to stripped periodic core",
                ],
                "why_interesting": (
                    f"same-core {row['family_law']} threshold-shift behavior "
                    "compares the actual denominator to its stripped periodic core"
                ),
                "related_open_claim_ids": _open_claim_ids(row),
            }
        )

    for row in phase_rows[: max(top, 4)]:
        score = 75
        if row["visibility_behavior"] == "rehiding_visible":
            score += 25
        if row["has_hidden_graph_obstruction_member"]:
            score += 15
        if row["has_visible_preimage_compression_member"]:
            score += 15
        rows.append(
            {
                "group": "same_core_signal",
                "source_surface": "same_core_obstruction_phase",
                "signal_class": "same_core_drift",
                "visibility_signal_score": score,
                "base": row["base"],
                "actual_n": row["selected_members"][-1],
                "core_n": row["core_n"],
                "members": row["selected_members"],
                "selected_obstruction_classes": row["selected_obstruction_classes"],
                "visibility_behavior": row["visibility_behavior"],
                "phase_summary": row["phase_summary"],
                "hidden_visible_switch_count": row["hidden_visible_switch_count"],
                "score_reasons": [
                    "same-core family changes state-map visibility behavior",
                    str(row["phase_summary"]),
                ],
                "why_interesting": row["phase_summary"],
                "related_open_claim_ids": _open_claim_ids(row),
            }
        )

    rows.sort(
        key=lambda row: (
            -int(row["visibility_signal_score"]),
            int(row["core_n"]),
            int(row["actual_n"]),
            str(row["source_surface"]),
        )
    )
    limit = max(top // 2, 4) if top > 0 else len(rows)
    return rows[:limit]


def visibility_optics_workbench_rows(
    max_n: int = 1200,
    *,
    base: int = 10,
    n_blocks: int = 8,
    top: int = 20,
) -> list[dict[str, object]]:
    """
    Rank finite-window evidence for the Visibility Optics research lens.

    The score is explicitly heuristic: it helps find cases where the source
    remainder orbit is more or less readable through the finite carry window.
    It does not promote `small_k_visibility_threshold` or
    `carry_dfa_factorization` beyond their open status.
    """
    visibility_rows = visibility_profile_rows(max_n, base=base, n_blocks=n_blocks)
    state_rows = state_merging_rows(max_n, base=base, n_blocks=n_blocks, max_m=8)
    state_by_coordinate = {
        (int(row["n"]), int(row["m"]), int(row["B"])): row for row in state_rows
    }

    candidate_rows: dict[tuple[int, int, int], dict[str, object]] = {}
    canonical_rows: list[dict[str, object]] = []

    for n, prefer_m in VISIBILITY_OPTICS_CANONICAL_ANCHORS.items():
        try:
            profile = carried_prefix_visibility_profile(
                n,
                base=base,
                n_blocks=n_blocks,
                prefer_m=prefer_m,
            )
        except ValueError:
            continue
        visibility_row = _profile_to_visibility_row(profile)
        state_row = state_by_coordinate.get((n, profile.m, profile.B))
        anchor = _visibility_optics_case_row(
            visibility_row=visibility_row,
            state_row=state_row,
            is_canonical_anchor=True,
            group="canonical_anchor",
        )
        if anchor is None:
            continue
        canonical_rows.append(anchor)
        candidate_rows[(n, profile.m, profile.B)] = {
            **anchor,
            "group": "ranked_case",
        }

    for visibility_row in visibility_rows:
        key = (
            int(visibility_row["n"]),
            int(visibility_row["m"]),
            int(visibility_row["B"]),
        )
        state_row = state_by_coordinate.get(key)
        candidate = _visibility_optics_case_row(
            visibility_row=visibility_row,
            state_row=state_row,
            is_canonical_anchor=False,
            group="ranked_case",
        )
        if candidate is None:
            continue
        previous = candidate_rows.get(key)
        if previous is None or int(candidate["visibility_signal_score"]) > int(previous["visibility_signal_score"]):
            candidate_rows[key] = candidate

    interesting_state_rows = [
        row
        for row in state_rows
        if row["obstruction_class"] != "state_relabeling"
        or int(row["n"]) in VISIBILITY_OPTICS_CANONICAL_ANCHORS
    ]
    interesting_state_rows.sort(
        key=lambda row: (
            {
                "hidden_graph_obstruction": 0,
                "visible_preimage_compression": 1,
                "finite_word_only": 2,
                "state_relabeling": 3,
            }[str(row["obstruction_class"])],
            int(row["k"]),
            int(row["n"]),
        )
    )
    for state_row in interesting_state_rows[: max(top * 5, 50)]:
        key = (int(state_row["n"]), int(state_row["m"]), int(state_row["B"]))
        try:
            profile = carried_prefix_visibility_profile(
                int(state_row["n"]),
                base=base,
                n_blocks=n_blocks,
                prefer_m=int(state_row["m"]),
            )
        except ValueError:
            continue
        visibility_row = _profile_to_visibility_row(profile)
        candidate = _visibility_optics_case_row(
            visibility_row=visibility_row,
            state_row=state_row,
            is_canonical_anchor=False,
            group="ranked_case",
        )
        if candidate is None:
            continue
        previous = candidate_rows.get(key)
        if previous is None or int(candidate["visibility_signal_score"]) > int(previous["visibility_signal_score"]):
            candidate_rows[key] = candidate

    best_by_n: dict[int, dict[str, object]] = {}
    for row in candidate_rows.values():
        n = int(row["n"])
        previous = best_by_n.get(n)
        if previous is None or int(row["visibility_signal_score"]) > int(previous["visibility_signal_score"]):
            best_by_n[n] = row

    ranked_rows = sorted(
        best_by_n.values(),
        key=lambda row: (
            -int(row["visibility_signal_score"]),
            int(row["k"]),
            int(row["n"]),
        ),
    )
    if top > 0:
        ranked_rows = ranked_rows[:top]

    same_core_rows = _same_core_optics_rows(
        max_n=max_n,
        base=base,
        n_blocks=n_blocks,
        top=top if top > 0 else 20,
    )
    summary = {
        "group": "workbench_summary",
        "base": base,
        "max_n": max_n,
        "n_blocks": n_blocks,
        "top": top,
        "visibility_profile_count": len(visibility_rows),
        "state_map_profile_count": len(state_rows),
        "ranked_case_count": len(ranked_rows),
        "same_core_signal_count": len(same_core_rows),
        "canonical_anchor_ns": list(VISIBILITY_OPTICS_CANONICAL_ANCHORS),
        "signal_classes": [
            "transparent_window",
            "early_carry_intrusion",
            "visible_state_compression",
            "hidden_graph_obstruction",
            "same_core_drift",
        ],
        "scoring_fields": [
            "raw_prefix_agreement_length",
            "first_incoming_carry_position",
            "first_local_overflow_position",
            "certified_lookahead_blocks",
            "factorization_regime",
            "obstruction_class",
            "preimage signatures",
        ],
        "open_claim_boundary": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
        "decision": (
            "Visibility Optics workbench rows are finite-window heuristic rankings; "
            "they do not prove global visibility or DFA factorization."
        ),
        **claim_context_for_parameters(
            (
                "small_k_visibility_threshold",
                "carry_dfa_factorization",
            ),
            base=base,
            requested_blocks=n_blocks,
        ),
    }
    return [summary, *canonical_rows, *ranked_rows, *same_core_rows]


def _best_visibility_cases_by_n(rows: list[dict[str, object]]) -> dict[int, dict[str, object]]:
    best_by_n: dict[int, dict[str, object]] = {}
    for row in rows:
        if row.get("group") not in {"canonical_anchor", "ranked_case"}:
            continue
        n = int(row["n"])
        previous = best_by_n.get(n)
        if previous is None or int(row["visibility_signal_score"]) > int(previous["visibility_signal_score"]):
            best_by_n[n] = row
    return best_by_n


def _base_signal_counts(cases_by_n: dict[int, dict[str, object]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in cases_by_n.values():
        signal_class = str(row["signal_class"])
        counts[signal_class] = counts.get(signal_class, 0) + 1
    return dict(sorted(counts.items()))


def _base_case_projection(row: dict[str, object]) -> dict[str, object]:
    return {
        "n": row["n"],
        "periodic_modulus": row["periodic_modulus"],
        "base": row["base"],
        "m": row["m"],
        "B": row["B"],
        "q": row["q"],
        "k": row["k"],
        "signal_class": row["signal_class"],
        "visibility_signal_score": row["visibility_signal_score"],
        "raw_prefix_agreement_length": row["raw_prefix_agreement_length"],
        "first_incoming_carry_position": row["first_incoming_carry_position"],
        "first_local_overflow_position": row["first_local_overflow_position"],
        "factorization_regime": row["factorization_regime"],
        "obstruction_class": row["obstruction_class"],
    }


def visibility_base_instrument_rows(
    max_n: int = 1200,
    *,
    bases: tuple[int, ...] = (10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
) -> list[dict[str, object]]:
    """
    Compare Visibility Optics workbench results across display bases.

    This is a base-instrument comparison surface: it asks which finite-window
    signal classes persist across bases and which appear to be created,
    removed, or shifted by changing the positional instrument. It is a bounded
    empirical probe, not a base-independent theorem.
    """
    unique_bases = tuple(dict.fromkeys(int(base) for base in bases if int(base) > 1))
    base_rows: dict[int, list[dict[str, object]]] = {}
    base_cases: dict[int, dict[int, dict[str, object]]] = {}
    base_summaries: list[dict[str, object]] = []

    for base in unique_bases:
        rows = visibility_optics_workbench_rows(
            max_n,
            base=base,
            n_blocks=n_blocks,
            top=top,
        )
        base_rows[base] = rows
        cases_by_n = _best_visibility_cases_by_n(rows)
        base_cases[base] = cases_by_n
        workbench_summary = next(row for row in rows if row["group"] == "workbench_summary")
        base_summaries.append(
            {
                "group": "base_summary",
                "base": base,
                "max_n": max_n,
                "n_blocks": n_blocks,
                "top": top,
                "visibility_profile_count": workbench_summary["visibility_profile_count"],
                "state_map_profile_count": workbench_summary["state_map_profile_count"],
                "ranked_case_count": workbench_summary["ranked_case_count"],
                "same_core_signal_count": workbench_summary["same_core_signal_count"],
                "signal_class_counts": _base_signal_counts(cases_by_n),
                "top_ranked_ns": [
                    int(row["n"])
                    for row in sorted(
                        cases_by_n.values(),
                        key=lambda case: (
                            -int(case["visibility_signal_score"]),
                            int(case["k"]),
                            int(case["n"]),
                        ),
                    )[: min(top, 8)]
                ],
                "related_open_claim_ids": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
            }
        )

    all_ns = sorted(
        {
            n
            for cases_by_n in base_cases.values()
            for n in cases_by_n
        }
    )
    cross_rows: list[dict[str, object]] = []
    for n in all_ns:
        present = {
            base: base_cases[base][n]
            for base in unique_bases
            if n in base_cases[base]
        }
        if len(present) < 2:
            continue
        signal_classes_by_base = {
            str(base): str(row["signal_class"]) for base, row in present.items()
        }
        periodic_moduli_by_base = {
            str(base): int(row["periodic_modulus"]) for base, row in present.items()
        }
        scores_by_base = {
            str(base): int(row["visibility_signal_score"]) for base, row in present.items()
        }
        distinct_signal_classes = sorted(set(signal_classes_by_base.values()))
        periodic_moduli = sorted(set(periodic_moduli_by_base.values()))
        if len(distinct_signal_classes) == 1:
            behavior = "base_stable_signal"
        elif 30 in present and len(periodic_moduli) > 1:
            behavior = "base30_absorption_shift"
        else:
            behavior = "instrument_shift"
        cross_rows.append(
            {
                "group": "cross_base_case",
                "n": n,
                "bases_present": list(present),
                "base_instrument_behavior": behavior,
                "signal_classes_by_base": signal_classes_by_base,
                "signal_class_path": " -> ".join(
                    f"{base}:{signal_classes_by_base[str(base)]}" for base in present
                ),
                "periodic_moduli_by_base": periodic_moduli_by_base,
                "scores_by_base": scores_by_base,
                "score_spread": max(scores_by_base.values()) - min(scores_by_base.values()),
                "case_projections": {
                    str(base): _base_case_projection(row) for base, row in present.items()
                },
                "why_interesting": (
                    "Changing the base instrument changes the finite-window signal class."
                    if behavior != "base_stable_signal"
                    else "The finite-window signal class persists across the selected base instruments."
                ),
                "related_open_claim_ids": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
            }
        )

    cross_rows.sort(
        key=lambda row: (
            row["base_instrument_behavior"] == "base_stable_signal",
            -int(row["score_spread"]),
            int(row["n"]),
        )
    )
    if top > 0:
        cross_rows = cross_rows[:top]

    base_ranked_rows: list[dict[str, object]] = []
    for base in unique_bases:
        ranked = sorted(
            base_cases[base].values(),
            key=lambda row: (
                -int(row["visibility_signal_score"]),
                int(row["k"]),
                int(row["n"]),
            ),
        )[: min(top, 8)]
        for row in ranked:
            base_ranked_rows.append(
                {
                    "group": "base_ranked_case",
                    "source_group": row["group"],
                    **_base_case_projection(row),
                    "why_interesting": row["why_interesting"],
                    "score_reasons": row["score_reasons"],
                    "related_open_claim_ids": row["related_open_claim_ids"],
                }
            )

    summary = {
        "group": "base_instrument_summary",
        "bases": list(unique_bases),
        "max_n": max_n,
        "n_blocks": n_blocks,
        "top": top,
        "base_count": len(unique_bases),
        "cross_base_case_count": len(cross_rows),
        "instrument_shift_count": sum(
            row["base_instrument_behavior"] != "base_stable_signal"
            for row in cross_rows
        ),
        "stable_signal_count": sum(
            row["base_instrument_behavior"] == "base_stable_signal"
            for row in cross_rows
        ),
        "open_claim_boundary": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
        "decision": (
            "Base-Instrument comparison treats bases as observation instruments: "
            "it reports which finite-window signal classes persist or change "
            "across selected bases without promoting a base-independent theorem."
        ),
        **claim_context_for_parameters(
            (
                "small_k_visibility_threshold",
                "carry_dfa_factorization",
            ),
            requested_blocks=n_blocks,
        ),
    }
    return [summary, *base_summaries, *cross_rows, *base_ranked_rows]


def _instrument_signal_lists(row: dict[str, object]) -> dict[str, list[int]]:
    projections = row["case_projections"]
    if not isinstance(projections, dict):
        raise TypeError("case_projections must be a dictionary")
    n = int(row["n"])
    bases_present = [int(base) for base in row["bases_present"]]
    reference_base = bases_present[0]
    reference_signal = str(projections[str(reference_base)]["signal_class"])

    transparent: list[int] = []
    revealed: list[int] = []
    carry_intrusion: list[int] = []
    obstructed: list[int] = []
    absorbed: list[int] = []
    distorted: list[int] = []
    for base in bases_present:
        projection = projections[str(base)]
        signal_class = str(projection["signal_class"])
        if signal_class == "transparent_window":
            transparent.append(base)
        if signal_class in {"transparent_window", "visible_state_compression"}:
            revealed.append(base)
        if signal_class == "early_carry_intrusion":
            carry_intrusion.append(base)
        if signal_class == "hidden_graph_obstruction":
            obstructed.append(base)
        if int(projection["periodic_modulus"]) != n:
            absorbed.append(base)
        if base != reference_base and signal_class != reference_signal:
            distorted.append(base)
    return {
        "transparent_bases": transparent,
        "revealed_by_bases": revealed,
        "carry_intrusion_bases": carry_intrusion,
        "obstructed_by_bases": obstructed,
        "absorbed_by_bases": absorbed,
        "distorted_from_reference_bases": distorted,
    }


def _instrument_axiom_pressure(row: dict[str, object], signal_lists: dict[str, list[int]]) -> list[str]:
    pressure: list[str] = []
    if signal_lists["distorted_from_reference_bases"]:
        pressure.append("recoverability_is_instrument_relative")
    if signal_lists["absorbed_by_bases"]:
        pressure.append("factor_absorption_changes_periodic_core")
    if signal_lists["revealed_by_bases"] and signal_lists["obstructed_by_bases"]:
        pressure.append("visible_trace_can_hide_state_obstruction")
    if signal_lists["transparent_bases"] and signal_lists["carry_intrusion_bases"]:
        pressure.append("transparent_prefix_is_not_base_absolute")
    if row["base_instrument_behavior"] == "base_stable_signal":
        pressure.append("candidate_base_stable_calibration_case")
    return pressure or ["mixed_instrument_signal"]


def _instrument_case_row(row: dict[str, object]) -> dict[str, object]:
    projections = row["case_projections"]
    if not isinstance(projections, dict):
        raise TypeError("case_projections must be a dictionary")
    signal_lists = _instrument_signal_lists(row)
    absorption_signature = " -> ".join(
        f"{base}:M={projections[str(base)]['periodic_modulus']}"
        for base in row["bases_present"]
    )
    pressure = _instrument_axiom_pressure(row, signal_lists)
    return {
        "group": "instrument_case",
        "n": row["n"],
        "bases_present": row["bases_present"],
        "base_instrument_behavior": row["base_instrument_behavior"],
        "instrument_signature": row["signal_class_path"],
        "absorption_signature": absorption_signature,
        "score_spread": row["score_spread"],
        **signal_lists,
        "case_projections": projections,
        "working_axiom_pressure": pressure,
        "why_interesting": (
            "This case pressures the current working vocabulary because its "
            "finite-window readability changes across base instruments."
            if row["base_instrument_behavior"] != "base_stable_signal"
            else "This case is a calibration anchor because the finite-window signal class persists."
        ),
        "related_open_claim_ids": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
    }


def _instrument_personality(counts: dict[str, int]) -> str:
    if counts["hidden_graph_case_count"] > 0:
        return "obstruction_revealer"
    if counts["absorbed_case_count"] >= max(1, counts["case_count"] // 2):
        return "absorptive_instrument"
    if counts["early_carry_case_count"] >= max(1, counts["revealed_case_count"]):
        return "carry_turbulent_instrument"
    if counts["revealed_case_count"] > counts["early_carry_case_count"]:
        return "transparent_instrument"
    return "mixed_instrument"


def _instrument_profile_rows(
    *,
    bases: tuple[int, ...],
    case_rows: list[dict[str, object]],
) -> list[dict[str, object]]:
    profiles: list[dict[str, object]] = []
    for base in bases:
        counts = {
            "case_count": 0,
            "transparent_case_count": 0,
            "revealed_case_count": 0,
            "early_carry_case_count": 0,
            "hidden_graph_case_count": 0,
            "absorbed_case_count": 0,
            "distorted_from_reference_count": 0,
        }
        example_ns: list[int] = []
        for row in case_rows:
            projections = row["case_projections"]
            if not isinstance(projections, dict) or str(base) not in projections:
                continue
            counts["case_count"] += 1
            example_ns.append(int(row["n"]))
            signal_class = str(projections[str(base)]["signal_class"])
            if signal_class == "transparent_window":
                counts["transparent_case_count"] += 1
            if signal_class in {"transparent_window", "visible_state_compression"}:
                counts["revealed_case_count"] += 1
            if signal_class == "early_carry_intrusion":
                counts["early_carry_case_count"] += 1
            if signal_class == "hidden_graph_obstruction":
                counts["hidden_graph_case_count"] += 1
            if base in row["absorbed_by_bases"]:
                counts["absorbed_case_count"] += 1
            if base in row["distorted_from_reference_bases"]:
                counts["distorted_from_reference_count"] += 1
        profiles.append(
            {
                "group": "instrument_profile",
                "base": base,
                **counts,
                "instrument_personality": _instrument_personality(counts),
                "example_ns": example_ns[:8],
                "related_open_claim_ids": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
            }
        )
    return profiles


def _working_axiom_signal_rows(case_rows: list[dict[str, object]]) -> list[dict[str, object]]:
    signals = [
        (
            "recoverability_is_instrument_relative",
            "Recoverability from the finite-window trace should be treated as a relation among denominator, base, block coordinate, and carry machine.",
        ),
        (
            "factor_absorption_changes_periodic_core",
            "A base that absorbs denominator factors can change the stripped periodic modulus, so absorption is an observed instrument effect rather than a universal simplification.",
        ),
        (
            "visible_trace_can_hide_state_obstruction",
            "A base can make a state-map obstruction visible, hidden, or irrelevant to the displayed finite trace.",
        ),
        (
            "candidate_base_stable_calibration_case",
            "Cases whose signal class persists across bases are useful calibration anchors for separating source behavior from instrument behavior.",
        ),
    ]
    rows: list[dict[str, object]] = []
    for signal_id, update in signals:
        examples = [
            int(row["n"])
            for row in case_rows
            if signal_id in row["working_axiom_pressure"]
        ]
        rows.append(
            {
                "group": "working_axiom_signal",
                "signal_id": signal_id,
                "evidence_count": len(examples),
                "example_ns": examples[:8],
                "working_axiom_update": update,
                "status": "empirical finite-window pressure, not a theorem claim",
                "related_open_claim_ids": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
            }
        )
    return rows


def instrument_atlas_rows(
    max_n: int = 1200,
    *,
    bases: tuple[int, ...] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
) -> list[dict[str, object]]:
    """
    Compare base instruments by what they reveal, absorb, or distort.

    The atlas is an empirical research surface built on the Visibility Optics
    workbench and base-instrument comparison. Its purpose is to pressure and
    refine working vocabulary, not to assert a base-independent theorem.
    """
    comparison_rows = visibility_base_instrument_rows(
        max_n,
        bases=bases,
        n_blocks=n_blocks,
        top=top,
    )
    comparison_summary = comparison_rows[0]
    unique_bases = tuple(int(base) for base in comparison_summary["bases"])
    source_cases = [
        row
        for row in comparison_rows
        if row["group"] == "cross_base_case"
    ]
    case_rows = [_instrument_case_row(row) for row in source_cases]
    profile_rows = _instrument_profile_rows(bases=unique_bases, case_rows=case_rows)
    axiom_rows = _working_axiom_signal_rows(case_rows)
    summary = {
        "group": "instrument_atlas_summary",
        "bases": list(unique_bases),
        "max_n": max_n,
        "n_blocks": n_blocks,
        "top": top,
        "instrument_profile_count": len(profile_rows),
        "instrument_case_count": len(case_rows),
        "working_axiom_signal_count": len(axiom_rows),
        "source_surface": "visibility-base-compare",
        "signal_vocabulary": [
            "reveal",
            "absorb",
            "distort",
            "obstruct",
            "calibrate",
        ],
        "open_claim_boundary": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
        "decision": (
            "Instrument Atlas rows compare bases as finite observation instruments. "
            "They identify pressure on working axioms without proving global "
            "visibility, preferred-base optimality, or DFA factorization."
        ),
        **claim_context_for_parameters(
            (
                "small_k_visibility_threshold",
                "carry_dfa_factorization",
            ),
            requested_blocks=n_blocks,
        ),
    }
    return [summary, *profile_rows, *case_rows, *axiom_rows]


def _projection_for_base(row: dict[str, object], base: int) -> dict[str, object] | None:
    projections = row["case_projections"]
    if not isinstance(projections, dict):
        raise TypeError("case_projections must be a dictionary")
    projection = projections.get(str(base))
    if projection is None:
        return None
    if not isinstance(projection, dict):
        raise TypeError("case projection must be a dictionary")
    return projection


def _chart_periodic_moduli(row: dict[str, object]) -> dict[str, int]:
    projections = row["case_projections"]
    if not isinstance(projections, dict):
        raise TypeError("case_projections must be a dictionary")
    return {
        str(base): int(projection["periodic_modulus"])
        for base, projection in projections.items()
        if isinstance(projection, dict)
    }


def _chart_signal_classes(row: dict[str, object]) -> dict[str, str]:
    projections = row["case_projections"]
    if not isinstance(projections, dict):
        raise TypeError("case_projections must be a dictionary")
    return {
        str(base): str(projection["signal_class"])
        for base, projection in projections.items()
        if isinstance(projection, dict)
    }


def _chart_case_class(row: dict[str, object]) -> str:
    signal_classes = set(_chart_signal_classes(row).values())
    periodic_moduli = set(_chart_periodic_moduli(row).values())
    if len(signal_classes) == 1 and len(periodic_moduli) == 1:
        return "clean_chart_invariant"
    if len(signal_classes) == 1:
        return "absorption_stable_signal"
    if len(periodic_moduli) == 1:
        return "clean_chart_distortion"
    return "absorption_shift_distortion"


def _chart_case_row(row: dict[str, object]) -> dict[str, object]:
    chart_class = _chart_case_class(row)
    periodic_moduli = _chart_periodic_moduli(row)
    return {
        "group": (
            "chart_invariant_case"
            if chart_class in {"clean_chart_invariant", "absorption_stable_signal"}
            else "chart_distortion_witness"
        ),
        "n": row["n"],
        "bases_present": row["bases_present"],
        "chart_invariance_class": chart_class,
        "chart_signature": row["instrument_signature"],
        "periodic_modulus_signature": " -> ".join(
            f"{base}:M={periodic_moduli[str(base)]}"
            for base in row["bases_present"]
        ),
        "signal_classes_by_base": _chart_signal_classes(row),
        "periodic_moduli_by_base": periodic_moduli,
        "score_spread": row["score_spread"],
        "absorbed_by_bases": row["absorbed_by_bases"],
        "working_axiom_pressure": row["working_axiom_pressure"],
        "why_interesting": {
            "clean_chart_invariant": (
                "The selected charts preserve both the stripped periodic modulus "
                "and the finite-window signal class."
            ),
            "absorption_stable_signal": (
                "The finite-window signal class persists even though some charts "
                "absorb base-supported factors."
            ),
            "clean_chart_distortion": (
                "The stripped periodic modulus is unchanged, but the finite-window "
                "signal class changes across charts."
            ),
            "absorption_shift_distortion": (
                "The finite-window signal changes while at least one chart also "
                "changes the stripped periodic modulus."
            ),
        }[chart_class],
        "related_open_claim_ids": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
    }


def _chart_pair_summary_rows(
    *,
    bases: tuple[int, ...],
    case_rows: list[dict[str, object]],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for left_index, left_base in enumerate(bases):
        for right_base in bases[left_index + 1:]:
            comparable = 0
            invariant = 0
            clean_invariant = 0
            absorption_invariant = 0
            distortion = 0
            clean_distortion = 0
            absorption_distortion = 0
            reveal_hide_flip = 0
            invariant_examples: list[int] = []
            distortion_examples: list[int] = []
            clean_distortion_examples: list[int] = []
            for row in case_rows:
                left = _projection_for_base(row, left_base)
                right = _projection_for_base(row, right_base)
                if left is None or right is None:
                    continue
                comparable += 1
                same_signal = str(left["signal_class"]) == str(right["signal_class"])
                same_modulus = int(left["periodic_modulus"]) == int(right["periodic_modulus"])
                n = int(row["n"])
                if same_signal:
                    invariant += 1
                    invariant_examples.append(n)
                    if same_modulus:
                        clean_invariant += 1
                    else:
                        absorption_invariant += 1
                else:
                    distortion += 1
                    distortion_examples.append(n)
                    if same_modulus:
                        clean_distortion += 1
                        clean_distortion_examples.append(n)
                    else:
                        absorption_distortion += 1
                signal_pair = {str(left["signal_class"]), str(right["signal_class"])}
                if "hidden_graph_obstruction" in signal_pair and signal_pair & {
                    "transparent_window",
                    "visible_state_compression",
                }:
                    reveal_hide_flip += 1
            if comparable == 0:
                relation_class = "no_comparable_cases"
                score = 0
            elif clean_distortion > 0:
                relation_class = "clean_chart_distortion_pair"
                score = round(1000 * invariant / comparable)
            elif absorption_distortion > 0:
                relation_class = "absorption_sensitive_pair"
                score = round(1000 * invariant / comparable)
            elif invariant == comparable:
                relation_class = "candidate_chart_invariant_pair"
                score = 1000
            else:
                relation_class = "mixed_chart_pair"
                score = round(1000 * invariant / comparable)
            rows.append(
                {
                    "group": "chart_pair_summary",
                    "left_base": left_base,
                    "right_base": right_base,
                    "base_pair": f"{left_base}/{right_base}",
                    "comparable_case_count": comparable,
                    "invariant_case_count": invariant,
                    "clean_invariant_case_count": clean_invariant,
                    "absorption_invariant_case_count": absorption_invariant,
                    "distortion_case_count": distortion,
                    "clean_distortion_case_count": clean_distortion,
                    "absorption_distortion_case_count": absorption_distortion,
                    "reveal_hide_flip_count": reveal_hide_flip,
                    "pair_invariance_score_per_mille": score,
                    "chart_relation_class": relation_class,
                    "invariant_example_ns": invariant_examples[:8],
                    "distortion_example_ns": distortion_examples[:8],
                    "clean_distortion_example_ns": clean_distortion_examples[:8],
                    "related_open_claim_ids": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
                }
            )
    rows.sort(
        key=lambda row: (
            {
                "clean_chart_distortion_pair": 0,
                "absorption_sensitive_pair": 1,
                "mixed_chart_pair": 2,
                "candidate_chart_invariant_pair": 3,
                "no_comparable_cases": 4,
            }[str(row["chart_relation_class"])],
            -int(row["clean_distortion_case_count"]),
            -int(row["distortion_case_count"]),
            -int(row["comparable_case_count"]),
            int(row["left_base"]),
            int(row["right_base"]),
        )
    )
    return rows


def chart_invariance_rows(
    max_n: int = 1200,
    *,
    bases: tuple[int, ...] = (7, 10, 12, 30),
    n_blocks: int = 8,
    top: int = 20,
) -> list[dict[str, object]]:
    """
    Empirically compare when base charts preserve finite-window visibility.

    Chart-invariance here is bounded evidence: two instruments look equivalent
    only on the selected finite row set, selected bases, and selected window.
    The output is meant to find candidate invariants and sharp distortion
    witnesses, not to assert a theorem.
    """
    atlas_rows = instrument_atlas_rows(
        max_n,
        bases=bases,
        n_blocks=n_blocks,
        top=top,
    )
    atlas_summary = atlas_rows[0]
    unique_bases = tuple(int(base) for base in atlas_summary["bases"])
    instrument_cases = [
        row
        for row in atlas_rows
        if row["group"] == "instrument_case"
    ]
    case_rows = [_chart_case_row(row) for row in instrument_cases]
    invariant_rows = [
        row
        for row in case_rows
        if row["group"] == "chart_invariant_case"
    ]
    distortion_rows = [
        row
        for row in case_rows
        if row["group"] == "chart_distortion_witness"
    ]
    pair_rows = _chart_pair_summary_rows(bases=unique_bases, case_rows=instrument_cases)
    summary = {
        "group": "chart_invariance_summary",
        "bases": list(unique_bases),
        "max_n": max_n,
        "n_blocks": n_blocks,
        "top": top,
        "source_surface": "instrument-atlas",
        "chart_pair_count": len(pair_rows),
        "chart_invariant_case_count": len(invariant_rows),
        "chart_distortion_witness_count": len(distortion_rows),
        "clean_chart_distortion_count": sum(
            row["chart_invariance_class"] == "clean_chart_distortion"
            for row in distortion_rows
        ),
        "chart_invariance_classes": [
            "clean_chart_invariant",
            "absorption_stable_signal",
            "clean_chart_distortion",
            "absorption_shift_distortion",
        ],
        "open_claim_boundary": list(VISIBILITY_OPTICS_OPEN_BOUNDARY),
        "decision": (
            "Chart-invariance rows are finite-window chart comparisons. They "
            "identify candidate invariant pairs and distortion witnesses without "
            "proving base-independent visibility or DFA factorization."
        ),
        **claim_context_for_parameters(
            (
                "small_k_visibility_threshold",
                "carry_dfa_factorization",
            ),
            requested_blocks=n_blocks,
        ),
    }
    distortion_rows.sort(
        key=lambda row: (
            row["chart_invariance_class"] != "clean_chart_distortion",
            -int(row["score_spread"]),
            int(row["n"]),
        )
    )
    invariant_rows.sort(
        key=lambda row: (
            row["chart_invariance_class"] != "clean_chart_invariant",
            -int(row["score_spread"]),
            int(row["n"]),
        )
    )
    if top > 0:
        distortion_rows = distortion_rows[:top]
        invariant_rows = invariant_rows[:top]
        pair_rows = pair_rows[:top]
    return [summary, *pair_rows, *distortion_rows, *invariant_rows]
