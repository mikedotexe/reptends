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
from .transducer import CarryTransition, carry_window_example


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
