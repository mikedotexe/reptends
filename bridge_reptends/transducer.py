"""
Carry propagation as a deterministic finite-window transducer.

For a finite coefficient word c_0, ..., c_{L-1}, the normalization step
that converts raw coefficients into base-B blocks is deterministic:

    state      = incoming carry from less significant blocks
    transition = (carry, c_j) -> floor((c_j + carry) / B)
    output     = normalized block value

This module packages that process explicitly so the repo can talk about the
carry layer using standard automata/transducer language instead of ad hoc
metaphor.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass

from .analysis import multiplicative_order
from .orbit_weave import apply_carry, raw_series_blocks, skeleton_vs_actual
from .orbit_weave import strip_base_factors
from .registry import claim_context_for_parameters


CANONICAL_ORBIT_CARRY_TRACE_MODES = {
    21: 6,
    97: 2,
    996: 3,
}


def _fiber_map(pairs: tuple[tuple[int, int], ...]) -> tuple[tuple[int, tuple[int, ...]], ...]:
    mapping: dict[int, set[int]] = {}
    for source, target in pairs:
        mapping.setdefault(source, set()).add(target)
    return tuple((source, tuple(sorted(targets))) for source, targets in sorted(mapping.items()))


def _preimage_fiber_map(
    fibers: tuple[tuple[int, tuple[int, ...]], ...],
) -> tuple[tuple[int, tuple[int, ...]], ...]:
    mapping: dict[int, set[int]] = {}
    for source, targets in fibers:
        for target in targets:
            mapping.setdefault(target, set()).add(source)
    return tuple((target, tuple(sorted(sources))) for target, sources in sorted(mapping.items()))


def _state_map_signature(
    entries: tuple[tuple[int, tuple[int, ...]], ...],
    *,
    arrow: str,
    empty: str,
) -> str:
    if not entries:
        return empty
    parts = [
        f"{state}{arrow}{','.join(str(value) for value in values)}"
        for state, values in entries
    ]
    return " | ".join(parts)


def _format_signed_gap(value: int) -> str:
    return f"{value:+d}"


@dataclass(frozen=True)
class CarryTransition:
    """One transducer transition for a single block."""

    position: int
    coefficient: int
    carry_in: int
    block_value: int
    carry_out: int


@dataclass(frozen=True)
class CarryRun:
    """A complete carry run over a finite coefficient word."""

    block_base: int
    transitions: tuple[CarryTransition, ...]

    @property
    def normalized_blocks(self) -> list[int]:
        return [transition.block_value for transition in self.transitions]

    @property
    def reachable_carries(self) -> tuple[int, ...]:
        carries = {transition.carry_in for transition in self.transitions}
        carries.update(transition.carry_out for transition in self.transitions)
        return tuple(sorted(carries))

    @property
    def state_trace(self) -> tuple[int, ...]:
        states = [transition.carry_in for transition in self.transitions]
        states.append(0)
        return tuple(states)

    def state_summary(self) -> CarryStateSummary:
        edge_counts = Counter(
            (
                transition.carry_in,
                transition.carry_out,
                transition.coefficient,
                transition.block_value,
            )
            for transition in self.transitions
        )
        edges = tuple(
            CarryGraphEdge(
                carry_in=carry_in,
                carry_out=carry_out,
                coefficient=coefficient,
                block_value=block_value,
                count=count,
            )
            for (carry_in, carry_out, coefficient, block_value), count in sorted(edge_counts.items())
        )
        first_nonzero_position = next(
            (
                transition.position
                for transition in self.transitions
                if transition.carry_in > 0 or transition.carry_out > 0
            ),
            None,
        )
        return CarryStateSummary(
            block_base=self.block_base,
            reachable_states=self.reachable_carries,
            first_nonzero_position=first_nonzero_position,
            edges=edges,
        )

    def to_dot(self) -> str:
        return self.state_summary().to_dot()

    def render(self, width: int) -> list[str]:
        """Render normalized blocks as zero-padded base-10 strings."""
        blocks = []
        for index, value in enumerate(self.normalized_blocks):
            if index == 0:
                blocks.append(str(value).zfill(width) if value < self.block_base else str(value))
            else:
                blocks.append(str(value).zfill(width))
        return blocks


@dataclass(frozen=True)
class CarryGraphEdge:
    """Unique edge in the observed carry-state graph."""

    carry_in: int
    carry_out: int
    coefficient: int
    block_value: int
    count: int


@dataclass(frozen=True)
class StateGraphEdge:
    """Edge in an observed deterministic state graph."""

    source: int
    target: int
    input_label: str
    output_label: str
    count: int


@dataclass(frozen=True)
class MinimizedStateGraph:
    """Coarse minimization of an observed deterministic state graph."""

    graph_kind: str
    initial_class: int
    classes: tuple[tuple[int, ...], ...]
    edges: tuple[StateGraphEdge, ...]

    @property
    def class_count(self) -> int:
        return len(self.classes)

    def to_dot(self) -> str:
        lines = [f"digraph Minimized{self.graph_kind}Graph {{"]
        lines.append("  rankdir=LR;")
        for index, members in enumerate(self.classes):
            label = ", ".join(str(member) for member in members)
            attrs = ' shape=doublecircle' if index == self.initial_class else ""
            lines.append(f'  "C{index}" [label="{label}"{attrs}];')
        for edge in self.edges:
            label = f"{edge.input_label} / {edge.output_label}"
            if edge.count > 1:
                label += f" ({edge.count})"
            lines.append(f'  "C{edge.source}" -> "C{edge.target}" [label="{label}"];')
        lines.append("}")
        return "\n".join(lines)


@dataclass(frozen=True)
class StateGraph:
    """Observed deterministic state graph for a finite run."""

    graph_kind: str
    initial_state: int
    states: tuple[int, ...]
    edges: tuple[StateGraphEdge, ...]

    @property
    def edge_count(self) -> int:
        return len(self.edges)

    @property
    def adjacency(self) -> dict[int, tuple[int, ...]]:
        mapping: dict[int, set[int]] = {}
        for edge in self.edges:
            mapping.setdefault(edge.source, set()).add(edge.target)
        return {state: tuple(sorted(targets)) for state, targets in sorted(mapping.items())}

    def outgoing_signature(self, state: int) -> tuple[tuple[str, str, int], ...]:
        return tuple(
            sorted(
                (
                    edge.input_label,
                    edge.output_label,
                    edge.target,
                )
                for edge in self.edges
                if edge.source == state
            )
        )

    def equivalence_classes(self) -> tuple[tuple[int, ...], ...]:
        buckets: dict[tuple[tuple[str, str, int], ...], list[int]] = {}
        for state in self.states:
            buckets.setdefault(self.outgoing_signature(state), []).append(state)
        return tuple(tuple(bucket) for _, bucket in sorted(buckets.items(), key=lambda item: item[1]))

    def minimize(self) -> MinimizedStateGraph:
        classes = self.equivalence_classes()
        state_to_class = {
            state: class_index
            for class_index, members in enumerate(classes)
            for state in members
        }
        edge_counts = Counter(
            (
                state_to_class[edge.source],
                state_to_class[edge.target],
                edge.input_label,
                edge.output_label,
            )
            for edge in self.edges
        )
        minimized_edges = tuple(
            StateGraphEdge(
                source=source,
                target=target,
                input_label=input_label,
                output_label=output_label,
                count=count,
            )
            for (source, target, input_label, output_label), count in sorted(edge_counts.items())
        )
        return MinimizedStateGraph(
            graph_kind=self.graph_kind,
            initial_class=state_to_class[self.initial_state],
            classes=classes,
            edges=minimized_edges,
        )

    def to_dot(self) -> str:
        lines = [f"digraph {self.graph_kind}StateGraph {{"]
        lines.append("  rankdir=LR;")
        for state in self.states:
            attrs = ' shape=doublecircle' if state == self.initial_state else ""
            lines.append(f'  "{state}"{attrs};')
        for edge in self.edges:
            label = f"{edge.input_label} / {edge.output_label}"
            if edge.count > 1:
                label += f" ({edge.count})"
            lines.append(f'  "{edge.source}" -> "{edge.target}" [label="{label}"];')
        lines.append("}")
        return "\n".join(lines)


@dataclass(frozen=True)
class CarryStateSummary:
    """Reachable-state summary of a carry run."""

    block_base: int
    reachable_states: tuple[int, ...]
    first_nonzero_position: int | None
    edges: tuple[CarryGraphEdge, ...]

    @property
    def max_carry(self) -> int:
        return self.reachable_states[-1] if self.reachable_states else 0

    @property
    def edge_count(self) -> int:
        return len(self.edges)

    @property
    def adjacency(self) -> dict[int, tuple[int, ...]]:
        mapping: dict[int, set[int]] = {}
        for edge in self.edges:
            mapping.setdefault(edge.carry_in, set()).add(edge.carry_out)
        return {state: tuple(sorted(targets)) for state, targets in sorted(mapping.items())}

    def graph(self) -> StateGraph:
        return StateGraph(
            graph_kind="CarryTransducer",
            initial_state=0,
            states=self.reachable_states,
            edges=tuple(
                StateGraphEdge(
                    source=edge.carry_in,
                    target=edge.carry_out,
                    input_label=f"c={edge.coefficient}",
                    output_label=f"out={edge.block_value}",
                    count=edge.count,
                )
                for edge in self.edges
            ),
        )

    def equivalence_classes(self) -> tuple[tuple[int, ...], ...]:
        return self.graph().equivalence_classes()

    def minimize(self) -> MinimizedStateGraph:
        return self.graph().minimize()

    def to_dot(self) -> str:
        return self.graph().to_dot()


@dataclass(frozen=True)
class RemainderTransition:
    """One long-division DFA transition for block base B."""

    position: int
    remainder_in: int
    block_value: int
    remainder_out: int


@dataclass(frozen=True)
class RemainderRun:
    """Finite run of the long-division DFA in block coordinates."""

    modulus: int
    block_base: int
    transitions: tuple[RemainderTransition, ...]

    @property
    def reachable_remainders(self) -> tuple[int, ...]:
        remainders = {transition.remainder_in for transition in self.transitions}
        remainders.update(transition.remainder_out for transition in self.transitions)
        return tuple(sorted(remainders))

    @property
    def state_trace(self) -> tuple[int, ...]:
        if not self.transitions:
            return (1,)
        states = [transition.remainder_in for transition in self.transitions]
        states.append(self.transitions[-1].remainder_out)
        return tuple(states)

    def render(self, width: int) -> list[str]:
        return [str(transition.block_value).zfill(width) for transition in self.transitions]

    def graph(self) -> StateGraph:
        edge_counts = Counter(
            (
                transition.remainder_in,
                transition.remainder_out,
                transition.position,
                transition.block_value,
            )
            for transition in self.transitions
        )
        return StateGraph(
            graph_kind="RemainderDFA",
            initial_state=self.transitions[0].remainder_in if self.transitions else 1,
            states=self.reachable_remainders,
            edges=tuple(
                StateGraphEdge(
                    source=remainder_in,
                    target=remainder_out,
                    input_label=f"step={position}",
                    output_label=f"out={block_value}",
                    count=count,
                )
                for (remainder_in, remainder_out, position, block_value), count in sorted(edge_counts.items())
            ),
        )

    def to_dot(self) -> str:
        return self.graph().to_dot()


@dataclass(frozen=True)
class StateAlignment:
    """Positionwise comparison between carry states and remainder states."""

    position: int
    coefficient: int
    carry_state: int
    remainder_state: int
    block_value: int


@dataclass(frozen=True)
class CoefficientConflictWitness:
    """A repeated remainder state with incompatible raw coefficients."""

    remainder_state: int
    positions: tuple[int, ...]
    coefficients: tuple[int, ...]
    carry_states: tuple[int, ...]
    block_values: tuple[int, ...]
    position_gap: int
    coefficient_delta: int
    output_hidden: bool


@dataclass(frozen=True)
class ObservedStateMap:
    """Observed state-map candidate extracted from aligned finite windows."""

    source_kind: str
    target_kind: str
    fibers: tuple[tuple[int, tuple[int, ...]], ...]

    @property
    def source_state_count(self) -> int:
        return len(self.fibers)

    @property
    def image_state_count(self) -> int:
        return len(self.preimage_fibers)

    @property
    def max_fiber_size(self) -> int:
        if not self.fibers:
            return 0
        return max(len(targets) for _, targets in self.fibers)

    @property
    def preimage_fibers(self) -> tuple[tuple[int, tuple[int, ...]], ...]:
        return _preimage_fiber_map(self.fibers)

    @property
    def max_preimage_size(self) -> int:
        if not self.preimage_fibers:
            return 0
        return max(len(sources) for _, sources in self.preimage_fibers)

    @property
    def ambiguous_sources(self) -> tuple[tuple[int, tuple[int, ...]], ...]:
        return tuple((source, targets) for source, targets in self.fibers if len(targets) > 1)

    @property
    def compression_targets(self) -> tuple[tuple[int, tuple[int, ...]], ...]:
        return tuple((target, sources) for target, sources in self.preimage_fibers if len(sources) > 1)

    @property
    def is_functional(self) -> bool:
        return all(len(targets) <= 1 for _, targets in self.fibers)

    @property
    def is_injective(self) -> bool:
        return self.is_functional and self.max_preimage_size <= 1

    @property
    def fiber_signature(self) -> str:
        return _state_map_signature(self.fibers, arrow="->", empty="empty")

    @property
    def preimage_signature(self) -> str:
        return _state_map_signature(self.preimage_fibers, arrow="<-", empty="empty")

    @property
    def ambiguity_signature(self) -> str:
        return _state_map_signature(self.ambiguous_sources, arrow="->", empty="functional")

    def export(self) -> dict[str, object]:
        return {
            "source_kind": self.source_kind,
            "target_kind": self.target_kind,
            "source_state_count": self.source_state_count,
            "image_state_count": self.image_state_count,
            "is_functional": self.is_functional,
            "is_injective": self.is_injective,
            "max_fiber_size": self.max_fiber_size,
            "max_preimage_size": self.max_preimage_size,
            "fiber_signature": self.fiber_signature,
            "preimage_signature": self.preimage_signature,
            "ambiguity_signature": self.ambiguity_signature,
            "fibers": [
                {
                    "source_state": source,
                    "target_states": list(targets),
                }
                for source, targets in self.fibers
            ],
            "preimage_fibers": [
                {
                    "target_state": target,
                    "source_states": list(sources),
                }
                for target, sources in self.preimage_fibers
            ],
            "compression_targets": [
                {
                    "target_state": target,
                    "source_states": list(sources),
                    "preimage_size": len(sources),
                }
                for target, sources in self.compression_targets
            ],
            "ambiguous_sources": [
                {
                    "source_state": source,
                    "target_states": list(targets),
                }
                for source, targets in self.ambiguous_sources
            ],
        }

    def summary_line(self) -> str:
        return (
            f"{self.source_kind} -> {self.target_kind}: finite-window functional criterion={self.is_functional}, "
            f"injective={self.is_injective}, max fiber size={self.max_fiber_size}, "
            f"max preimage size={self.max_preimage_size}"
        )


@dataclass(frozen=True)
class FactorizationDecisionReport:
    """Decision-complete local framework for the open carry/DFA claim."""

    outputs_match: bool
    carry_state_count: int
    remainder_state_count: int
    carry_class_count: int
    remainder_class_count: int
    remainder_to_carry_map: ObservedStateMap
    carry_to_remainder_map: ObservedStateMap

    @property
    def graph_state_count_match(self) -> bool:
        return self.carry_state_count == self.remainder_state_count

    @property
    def minimized_class_count_match(self) -> bool:
        return self.carry_class_count == self.remainder_class_count

    @property
    def graph_state_gap(self) -> int:
        return self.carry_state_count - self.remainder_state_count

    @property
    def minimized_class_gap(self) -> int:
        return self.carry_class_count - self.remainder_class_count

    @property
    def observed_alignment_bijection(self) -> bool:
        return self.remainder_to_carry_map.is_injective and self.carry_to_remainder_map.is_injective

    @property
    def compression_targets(self) -> tuple[tuple[int, tuple[int, ...]], ...]:
        return self.remainder_to_carry_map.compression_targets

    @property
    def state_relabeling_candidate(self) -> bool:
        return (
            self.outputs_match
            and self.graph_state_count_match
            and self.minimized_class_count_match
            and self.remainder_to_carry_map.is_injective
            and self.carry_to_remainder_map.is_injective
        )

    @property
    def remainder_to_carry_quotient_candidate(self) -> bool:
        return self.outputs_match and self.remainder_to_carry_map.is_functional

    @property
    def carry_to_remainder_lift_candidate(self) -> bool:
        return self.outputs_match and self.carry_to_remainder_map.is_functional

    @property
    def counterexample_to_state_relabeling(self) -> bool:
        return self.outputs_match and not self.state_relabeling_candidate

    @property
    def regime(self) -> str:
        if self.state_relabeling_candidate:
            return "state_relabeling"
        if self.remainder_to_carry_quotient_candidate:
            return "quotient_candidate_only"
        return "finite_word_only"

    @property
    def obstruction_class(self) -> str:
        if self.regime == "state_relabeling":
            return "state_relabeling"
        if self.regime == "finite_word_only":
            return "finite_word_only"
        if self.remainder_to_carry_map.max_preimage_size > 1:
            return "visible_preimage_compression"
        if self.observed_alignment_bijection:
            return "hidden_graph_obstruction"
        return "visible_preimage_compression"

    @property
    def obstruction_summary(self) -> str:
        if self.obstruction_class == "state_relabeling":
            return (
                "The aligned window stays bijective in both directions, so the selected coordinate "
                "still looks like a genuine finite-window relabeling."
            )
        if self.obstruction_class == "finite_word_only":
            return (
                "The selected window already fails the forward remainder-to-carry functional criterion, "
                "so the obstruction appears before any quotient candidate."
            )
        if self.obstruction_class == "visible_preimage_compression":
            targets = ", ".join(str(target) for target, _ in self.compression_targets)
            return (
                "The selected window visibly compresses multiple remainder states onto carry state"
                f"{'' if len(self.compression_targets) == 1 else 's'} {targets}, so relabeling already "
                "fails at the preimage-fiber level."
            )
        return (
            "The aligned window is bijective, but the observed carry/remainder graph gaps "
            f"({_format_signed_gap(self.graph_state_gap)} states, "
            f"{_format_signed_gap(self.minimized_class_gap)} minimized classes) keep the obstruction "
            "in graph structure rather than visible compression."
        )

    @property
    def theorem_target(self) -> str:
        return (
            "Promote finite-window agreement to a canonical state-level factorization, ideally by a "
            "global remainder-to-carry morphism that explains the displayed word for every coprime modulus."
        )

    @property
    def refutation_target(self) -> str:
        return (
            "Find a bounded example where the displayed words agree on the visible window but even the "
            "observed finite-window remainder-to-carry functional criterion fails, or where the observed "
            "transition data becomes incompatible with any simple state relabeling."
        )

    @property
    def weaker_replacement(self) -> str:
        return (
            "If a canonical factorization fails, downgrade to finite-window output agreement plus observed "
            "finite functional criteria and a quotient-from-remainder-to-carry framework, without claiming "
            "a unique global state factorization."
        )

    def summary_lines(self) -> tuple[str, ...]:
        return (
            f"finite-window word agreement = {self.outputs_match}",
            f"carry/remainder state counts = {self.carry_state_count}/{self.remainder_state_count}",
            f"state-count match = {self.graph_state_count_match}",
            f"carry/remainder class counts = {self.carry_class_count}/{self.remainder_class_count}",
            f"minimized-class-count match = {self.minimized_class_count_match}",
            self.remainder_to_carry_map.summary_line(),
            self.carry_to_remainder_map.summary_line(),
            f"observed alignment bijection = {self.observed_alignment_bijection}",
            f"factorization regime = {self.regime}",
            f"obstruction class = {self.obstruction_class}",
            f"state-relabeling candidate holds = {self.state_relabeling_candidate}",
            f"remainder-to-carry quotient candidate holds = {self.remainder_to_carry_quotient_candidate}",
            f"carry-to-remainder lift candidate holds = {self.carry_to_remainder_lift_candidate}",
        )


@dataclass(frozen=True)
class FactorizationSelectorStep:
    """One candidate block coordinate in the Track 17 selector scan."""

    m: int
    B: int
    q: int
    k: int
    regime: str
    state_relabeling_candidate: bool
    remainder_to_carry_quotient_candidate: bool
    carry_to_remainder_lift_candidate: bool


@dataclass(frozen=True)
class CarryFactorizationSelectorProfile:
    """Regime profile across candidate block widths for one denominator."""

    n: int
    base: int
    n_blocks: int
    steps: tuple[FactorizationSelectorStep, ...]

    @property
    def selected_m(self) -> int | None:
        if not self.steps:
            return None
        step = min(
            self.steps,
            key=lambda step: (
                {
                    "state_relabeling": 0,
                    "quotient_candidate_only": 1,
                    "finite_word_only": 2,
                }[step.regime],
                step.k,
                step.m,
                step.B,
            ),
        )
        return step.m

    @property
    def selected_step(self) -> FactorizationSelectorStep | None:
        if self.selected_m is None:
            return None
        return next(step for step in self.steps if step.m == self.selected_m)

    @property
    def relabeling_modes(self) -> tuple[int, ...]:
        return tuple(step.m for step in self.steps if step.regime == "state_relabeling")

    @property
    def quotient_modes(self) -> tuple[int, ...]:
        return tuple(step.m for step in self.steps if step.regime == "quotient_candidate_only")

    @property
    def finite_word_only_modes(self) -> tuple[int, ...]:
        return tuple(step.m for step in self.steps if step.regime == "finite_word_only")

    @property
    def transition_signature(self) -> tuple[str, ...]:
        signature: list[str] = []
        for step in self.steps:
            if not signature or signature[-1] != step.regime:
                signature.append(step.regime)
        return tuple(signature)

    @property
    def has_isolated_relabeling_window(self) -> bool:
        return bool(self.relabeling_modes) and self.transition_signature.count("state_relabeling") == 1 and len(self.transition_signature) > 1

    @property
    def selector_summary_lines(self) -> tuple[str, ...]:
        return (
            f"selector modes scanned = {[step.m for step in self.steps]}",
            f"transition signature = {self.transition_signature}",
            f"relabeling modes = {self.relabeling_modes}",
            f"quotient modes = {self.quotient_modes}",
            f"finite-word-only modes = {self.finite_word_only_modes}",
            f"selected m = {self.selected_m}",
        )


@dataclass(frozen=True)
class SelectorProfileComparison:
    """Comparison between two selector profiles, typically in one family."""

    left_n: int
    right_n: int
    base: int
    left_profile: CarryFactorizationSelectorProfile
    right_profile: CarryFactorizationSelectorProfile
    shared_periodic_core: int | None

    @property
    def common_relabeling_modes(self) -> tuple[int, ...]:
        return tuple(sorted(set(self.left_profile.relabeling_modes) & set(self.right_profile.relabeling_modes)))

    @property
    def left_only_relabeling_modes(self) -> tuple[int, ...]:
        return tuple(sorted(set(self.left_profile.relabeling_modes) - set(self.right_profile.relabeling_modes)))

    @property
    def right_only_relabeling_modes(self) -> tuple[int, ...]:
        return tuple(sorted(set(self.right_profile.relabeling_modes) - set(self.left_profile.relabeling_modes)))

    @property
    def relabeling_window_destroyed(self) -> bool:
        return bool(self.left_profile.relabeling_modes) and not self.right_profile.relabeling_modes

    @property
    def relabeling_window_created(self) -> bool:
        return not self.left_profile.relabeling_modes and bool(self.right_profile.relabeling_modes)

    @property
    def relabeling_window_shifted(self) -> bool:
        return (
            bool(self.left_profile.relabeling_modes)
            and bool(self.right_profile.relabeling_modes)
            and self.left_profile.relabeling_modes != self.right_profile.relabeling_modes
        )

    @property
    def transition_signature_changed(self) -> bool:
        return self.left_profile.transition_signature != self.right_profile.transition_signature

    def summary_lines(self) -> tuple[str, ...]:
        return (
            f"left/right = {self.left_n}/{self.right_n} in base {self.base}",
            f"shared periodic core = {self.shared_periodic_core}",
            f"left signature = {self.left_profile.transition_signature}",
            f"right signature = {self.right_profile.transition_signature}",
            f"common relabeling modes = {self.common_relabeling_modes}",
            f"left-only relabeling modes = {self.left_only_relabeling_modes}",
            f"right-only relabeling modes = {self.right_only_relabeling_modes}",
            f"relabeling window destroyed = {self.relabeling_window_destroyed}",
            f"relabeling window created = {self.relabeling_window_created}",
            f"relabeling window shifted = {self.relabeling_window_shifted}",
        )


@dataclass(frozen=True)
class CarrySelectorCaseStudy:
    """Named selector-profile case study for Track 17."""

    label: str
    n: int
    base: int
    explanation: str
    theorem_candidate: str
    heuristic_note: str
    counterexample_target: str
    primary_vocabulary_id: str
    profile: CarryFactorizationSelectorProfile


@dataclass(frozen=True)
class CarrySelectorFamilyStudy:
    """Named selector-profile family study for Track 17."""

    label: str
    members: tuple[int, ...]
    explanation: str
    theorem_candidate: str
    heuristic_note: str
    counterexample_target: str
    primary_vocabulary_id: str
    summary_lines: tuple[str, ...] = ()


@dataclass(frozen=True)
class StateMergingCaseStudy:
    """Named preimage-fiber profile case study on the selected Track 17 coordinate."""

    label: str
    n: int
    base: int
    explanation: str
    theorem_candidate: str
    heuristic_note: str
    counterexample_target: str
    primary_vocabulary_id: str
    profile: CarryFactorizationSelectorProfile
    comparison: CarryRemainderComparison


@dataclass(frozen=True)
class StateMergingFamilyStudy:
    """Named preimage-fiber profile family study for the selected coordinates."""

    label: str
    members: tuple[int, ...]
    explanation: str
    theorem_candidate: str
    heuristic_note: str
    counterexample_target: str
    primary_vocabulary_id: str
    member_cases: tuple[StateMergingCaseStudy, ...]
    summary_lines: tuple[str, ...] = ()


def carry_selector_research_rows(
    classification_bound: int = 120,
    *,
    bases: tuple[int, ...] = (7, 10, 12),
    n_blocks: int = 8,
    max_m: int = 8,
    sample_size: int = 5,
    max_block_base: int = 10_000_000,
) -> list[dict[str, object]]:
    """Cross-base Track 17 summary rows for the published atlas research layer."""
    rows: list[dict[str, object]] = []
    for base in bases:
        profiles = carry_selector_profile_rows(
            classification_bound,
            base=base,
            n_blocks=n_blocks,
            max_m=max_m,
            max_block_base=max_block_base,
        )
        class_counts = Counter(str(row["profile_class"]) for row in profiles)
        non_k_one = [
            row
            for row in profiles
            if str(row["selected_regime"]) == "state_relabeling" and int(row["selected_k"]) > 1
        ]
        families = same_core_selector_family_rows(
            classification_bound,
            base=base,
            n_blocks=n_blocks,
            max_m=max_m,
            max_block_base=max_block_base,
        )
        disagreements = [
            row
            for row in families
            if bool(row["has_relabeling_disagreement"]) or bool(row["has_signature_disagreement"])
        ]
        multi_member = [row for row in disagreements if len(list(row["selected_members"])) >= 2]
        sample_non_k_one = [
            f"N={int(row['n'])} @ m={int(row['selected_m'])} with k={int(row['selected_k'])}"
            for row in non_k_one[:sample_size]
        ]
        sample_families = [
            f"core {int(row['core_n'])}: members {list(row['members'])}, selected {list(row['selected_members'])}"
            for row in (multi_member or disagreements)[:sample_size]
        ]
        rows.append(
            {
                "base": base,
                "classification_bound": classification_bound,
                "n_blocks": n_blocks,
                "max_m": max_m,
                "profile_count": len(profiles),
                "isolated_non_k_one_relabeling": class_counts["isolated_non_k_one_relabeling"],
                "repeated_non_k_one_relabeling": class_counts["repeated_non_k_one_relabeling"],
                "isolated_k_one_relabeling": class_counts["isolated_k_one_relabeling"],
                "repeated_k_one_relabeling": class_counts["repeated_k_one_relabeling"],
                "mixed_without_relabeling": class_counts["mixed_without_relabeling"],
                "quotient_only": class_counts["quotient_only"],
                "finite_word_only": class_counts["finite_word_only"],
                "non_k_one_count": len(non_k_one),
                "same_core_disagreement_count": len(disagreements),
                "same_core_multi_member_count": len(multi_member),
                "sample_non_k_one_examples": sample_non_k_one,
                "sample_same_core_families": sample_families,
                "publication_decision": "published_research_layer",
                "summary_lines": [
                    f"base {base}: {len(non_k_one)} selected non-k = 1 relabeling windows up to N <= {classification_bound}",
                    f"same-core disagreement groups = {len(disagreements)}",
                    (
                        f"multi-member same-core relabeling families = {len(multi_member)}"
                        if multi_member
                        else "no multi-member same-core relabeling families appear in this bounded sweep"
                    ),
                ],
            }
        )
    return rows


def _factorization_mode_priority(comparison: "CarryRemainderComparison") -> tuple[int, int, int, int]:
    regime_rank = {
        "state_relabeling": 0,
        "quotient_candidate_only": 1,
        "finite_word_only": 2,
    }[comparison.decision_report.regime]
    return (
        regime_rank,
        comparison.k,
        comparison.m,
        comparison.B,
    )


def select_carry_factorization_prefer_m(
    n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_m: int = 12,
    max_block_base: int = 10_000_000,
) -> int | None:
    """Pick the most informative block coordinate for Track 17 regime search."""
    profile = carry_factorization_selector_profile(
        n,
        base=base,
        n_blocks=n_blocks,
        max_m=max_m,
        max_block_base=max_block_base,
    )
    return profile.selected_m


def carry_factorization_selector_profile(
    n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_m: int = 12,
    max_block_base: int = 10_000_000,
) -> CarryFactorizationSelectorProfile:
    """Scan candidate block widths and record Track 17 regime transitions."""
    steps: list[FactorizationSelectorStep] = []
    for m in range(1, max_m + 1):
        try:
            comparison = carry_remainder_comparison(
                n,
                base=base,
                n_blocks=n_blocks,
                prefer_m=m,
            )
        except Exception:
            continue
        if comparison.q <= 0 or comparison.B > max_block_base:
            continue
        report = comparison.decision_report
        steps.append(
            FactorizationSelectorStep(
                m=m,
                B=comparison.B,
                q=comparison.q,
                k=comparison.k,
                regime=report.regime,
                state_relabeling_candidate=report.state_relabeling_candidate,
                remainder_to_carry_quotient_candidate=report.remainder_to_carry_quotient_candidate,
                carry_to_remainder_lift_candidate=report.carry_to_remainder_lift_candidate,
            )
        )
    return CarryFactorizationSelectorProfile(
        n=n,
        base=base,
        n_blocks=n_blocks,
        steps=tuple(steps),
    )


def compare_carry_selector_profiles(
    left_n: int,
    right_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_m: int = 12,
    max_block_base: int = 10_000_000,
) -> SelectorProfileComparison:
    """Compare two selector profiles in the same base."""
    left = carry_factorization_selector_profile(
        left_n,
        base=base,
        n_blocks=n_blocks,
        max_m=max_m,
        max_block_base=max_block_base,
    )
    right = carry_factorization_selector_profile(
        right_n,
        base=base,
        n_blocks=n_blocks,
        max_m=max_m,
        max_block_base=max_block_base,
    )
    left_core, _ = strip_base_factors(left_n, base)
    right_core, _ = strip_base_factors(right_n, base)
    shared_core = left_core if left_core == right_core else None
    return SelectorProfileComparison(
        left_n=left_n,
        right_n=right_n,
        base=base,
        left_profile=left,
        right_profile=right,
        shared_periodic_core=shared_core,
    )


def carry_selector_profile_class(profile: CarryFactorizationSelectorProfile) -> str:
    """Classify a selector profile into a small Track 17 research taxonomy."""
    selected = profile.selected_step
    if selected is None:
        return "no_profile"
    if selected.regime == "state_relabeling":
        prefix = "k_one" if selected.k == 1 else "non_k_one"
        if profile.has_isolated_relabeling_window:
            return f"isolated_{prefix}_relabeling"
        if len(profile.relabeling_modes) > 1:
            return f"repeated_{prefix}_relabeling"
        return f"{prefix}_relabeling"
    if profile.quotient_modes and profile.finite_word_only_modes:
        return "mixed_without_relabeling"
    if profile.quotient_modes:
        return "quotient_only"
    if profile.finite_word_only_modes:
        return "finite_word_only"
    return "unclassified"


def carry_selector_profile_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_m: int = 12,
    max_block_base: int = 10_000_000,
) -> list[dict[str, object]]:
    """Export selector profiles as a stable research/search surface."""
    rows: list[dict[str, object]] = []
    for n in range(2, max_n + 1):
        profile = carry_factorization_selector_profile(
            n,
            base=base,
            n_blocks=n_blocks,
            max_m=max_m,
            max_block_base=max_block_base,
        )
        selected = profile.selected_step
        if selected is None:
            continue
        rows.append(
            {
                "n": n,
                "base": base,
                "selected_m": profile.selected_m,
                "selected_B": selected.B,
                "selected_q": selected.q,
                "selected_k": selected.k,
                "selected_regime": selected.regime,
                "profile_class": carry_selector_profile_class(profile),
                "transition_signature": list(profile.transition_signature),
                "relabeling_modes": list(profile.relabeling_modes),
                "quotient_modes": list(profile.quotient_modes),
                "finite_word_only_modes": list(profile.finite_word_only_modes),
                "has_isolated_relabeling_window": profile.has_isolated_relabeling_window,
            }
        )
    class_rank = {
        "isolated_non_k_one_relabeling": 0,
        "repeated_non_k_one_relabeling": 1,
        "non_k_one_relabeling": 2,
        "isolated_k_one_relabeling": 3,
        "repeated_k_one_relabeling": 4,
        "k_one_relabeling": 5,
        "mixed_without_relabeling": 6,
        "quotient_only": 7,
        "finite_word_only": 8,
        "unclassified": 9,
        "no_profile": 10,
    }
    rows.sort(
        key=lambda row: (
            class_rank[str(row["profile_class"])],
            int(row["selected_k"]),
            int(row["selected_m"]),
            int(row["n"]),
        )
    )
    return rows


def non_k_one_state_relabeling_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_m: int = 12,
    max_block_base: int = 10_000_000,
) -> list[dict[str, object]]:
    """Rows where the selector chooses a non-k=1 state-relabeling window."""
    return [
        row
        for row in carry_selector_profile_rows(
            max_n,
            base=base,
            n_blocks=n_blocks,
            max_m=max_m,
            max_block_base=max_block_base,
        )
        if str(row["selected_regime"]) == "state_relabeling"
        and int(row["selected_k"]) > 1
    ]


def same_core_selector_family_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_m: int = 12,
    max_block_base: int = 10_000_000,
    require_disagreement: bool = True,
) -> list[dict[str, object]]:
    """Group selector profiles by stripped periodic core and summarize disagreement."""
    groups: dict[int, list[dict[str, object]]] = {}
    for row in carry_selector_profile_rows(
        max_n,
        base=base,
        n_blocks=n_blocks,
        max_m=max_m,
        max_block_base=max_block_base,
    ):
        core, _ = strip_base_factors(int(row["n"]), base)
        if core == 1:
            continue
        groups.setdefault(core, []).append(row)

    rows: list[dict[str, object]] = []
    for core, members in groups.items():
        if len(members) < 2:
            continue
        members.sort(key=lambda row: int(row["n"]))
        signatures = {tuple(row["transition_signature"]) for row in members}
        relabeling_modes = {tuple(int(mode) for mode in row["relabeling_modes"]) for row in members}
        regimes = {str(row["selected_regime"]) for row in members}
        profile_classes = {str(row["profile_class"]) for row in members}
        has_disagreement = len(signatures) > 1 or len(relabeling_modes) > 1 or len(regimes) > 1
        if require_disagreement and not has_disagreement:
            continue
        relabeling_members = [int(row["n"]) for row in members if row["relabeling_modes"]]
        rows.append(
            {
                "core_n": core,
                "base": base,
                "members": [int(row["n"]) for row in members],
                "selected_members": [int(row["n"]) for row in members if str(row["selected_regime"]) == "state_relabeling"],
                "relabeling_members": relabeling_members,
                "selected_regimes": [str(row["selected_regime"]) for row in members],
                "profile_classes": [str(row["profile_class"]) for row in members],
                "transition_signatures": [list(row["transition_signature"]) for row in members],
                "relabeling_mode_sets": [list(row["relabeling_modes"]) for row in members],
                "has_signature_disagreement": len(signatures) > 1,
                "has_relabeling_disagreement": len(relabeling_modes) > 1,
                "has_regime_disagreement": len(regimes) > 1,
                **claim_context_for_parameters(
                    ("carry_dfa_factorization",),
                    base=base,
                    actual=int(members[-1]["n"]),
                    core=core,
                    requested_blocks=n_blocks,
                ),
            }
        )
    rows.sort(
        key=lambda row: (
            not bool(row["selected_members"]),
            not bool(row["has_relabeling_disagreement"]),
            int(row["core_n"]),
        )
    )
    return rows


@dataclass(frozen=True)
class CarryRemainderComparison:
    """Finite-window comparison between carry normalization and long division."""

    n: int
    base: int
    m: int
    B: int
    q: int
    k: int
    lookahead_blocks: int
    carry_example: CarryWindowExample
    remainder_run: RemainderRun
    alignments: tuple[StateAlignment, ...]

    @property
    def carry_graph(self) -> StateGraph:
        return self.carry_example.run.state_summary().graph()

    @property
    def remainder_graph(self) -> StateGraph:
        return self.remainder_run.graph()

    @property
    def minimized_carry_graph(self) -> MinimizedStateGraph:
        return self.carry_graph.minimize()

    @property
    def minimized_remainder_graph(self) -> MinimizedStateGraph:
        return self.remainder_graph.minimize()

    @property
    def outputs_match(self) -> bool:
        return tuple(self.remainder_run.render(self.m)) == self.carry_example.carried_blocks

    @property
    def remainder_to_carry_map(self) -> ObservedStateMap:
        pairs = tuple((alignment.remainder_state, alignment.carry_state) for alignment in self.alignments)
        return ObservedStateMap(
            source_kind="remainder state",
            target_kind="carry state",
            fibers=_fiber_map(pairs),
        )

    @property
    def remainder_to_coefficient_map(self) -> ObservedStateMap:
        pairs = tuple((alignment.remainder_state, alignment.coefficient) for alignment in self.alignments)
        return ObservedStateMap(
            source_kind="remainder state",
            target_kind="raw coefficient",
            fibers=_fiber_map(pairs),
        )

    @property
    def remainder_to_coefficient_mod_block_base_map(self) -> ObservedStateMap:
        pairs = tuple(
            (alignment.remainder_state, alignment.coefficient % self.B)
            for alignment in self.alignments
        )
        return ObservedStateMap(
            source_kind="remainder state",
            target_kind="coefficient modulo block base",
            fibers=_fiber_map(pairs),
        )

    @property
    def remainder_to_carried_block_value_map(self) -> ObservedStateMap:
        pairs = tuple((alignment.remainder_state, alignment.block_value) for alignment in self.alignments)
        return ObservedStateMap(
            source_kind="remainder state",
            target_kind="carried block value",
            fibers=_fiber_map(pairs),
        )

    @property
    def carry_to_remainder_map(self) -> ObservedStateMap:
        pairs = tuple((alignment.carry_state, alignment.remainder_state) for alignment in self.alignments)
        return ObservedStateMap(
            source_kind="carry state",
            target_kind="remainder state",
            fibers=_fiber_map(pairs),
        )

    @property
    def coefficient_functional(self) -> bool:
        return self.remainder_to_coefficient_map.is_functional

    @property
    def remainder_to_coefficient_conflicts(self) -> tuple[CoefficientConflictWitness, ...]:
        conflicts: list[CoefficientConflictWitness] = []
        for remainder_state, _ in self.remainder_to_coefficient_map.ambiguous_sources:
            alignments = tuple(
                alignment
                for alignment in self.alignments
                if alignment.remainder_state == remainder_state
            )
            coefficients = tuple(alignment.coefficient for alignment in alignments)
            if len(set(coefficients)) <= 1:
                continue
            positions = tuple(alignment.position for alignment in alignments)
            carry_states = tuple(alignment.carry_state for alignment in alignments)
            block_values = tuple(alignment.block_value for alignment in alignments)
            conflicts.append(
                CoefficientConflictWitness(
                    remainder_state=remainder_state,
                    positions=positions,
                    coefficients=coefficients,
                    carry_states=carry_states,
                    block_values=block_values,
                    position_gap=max(positions) - min(positions),
                    coefficient_delta=max(coefficients) - min(coefficients),
                    output_hidden=len(set(block_values)) == 1,
                )
            )
        conflicts.sort(
            key=lambda conflict: (
                conflict.positions[0],
                conflict.remainder_state,
            )
        )
        return tuple(conflicts)

    @property
    def first_remainder_to_coefficient_conflict(self) -> CoefficientConflictWitness | None:
        conflicts = self.remainder_to_coefficient_conflicts
        return conflicts[0] if conflicts else None

    @property
    def decision_report(self) -> FactorizationDecisionReport:
        return FactorizationDecisionReport(
            outputs_match=self.outputs_match,
            carry_state_count=len(self.carry_graph.states),
            remainder_state_count=len(self.remainder_graph.states),
            carry_class_count=self.minimized_carry_graph.class_count,
            remainder_class_count=self.minimized_remainder_graph.class_count,
            remainder_to_carry_map=self.remainder_to_carry_map,
            carry_to_remainder_map=self.carry_to_remainder_map,
        )

    @property
    def alignment_rows(self) -> tuple[dict[str, int], ...]:
        return tuple(
            {
                "position": alignment.position,
                "coefficient": alignment.coefficient,
                "carry_state": alignment.carry_state,
                "remainder_state": alignment.remainder_state,
                "block_value": alignment.block_value,
            }
            for alignment in self.alignments
        )

    @property
    def implemented_statement(self) -> str:
        return (
            "finite-window output agreement between the carry-propagated block "
            "normalization and the long-division DFA"
        )

    @property
    def open_claim_boundary(self) -> str:
        return (
            "canonical factorization of the entire long-division DFA into orbit plus carry "
            "is not established here"
        )

    def summary_lines(self) -> tuple[str, ...]:
        return (
            f"N = {self.n}, base = {self.base}, block base B = {self.B}",
            f"q = {self.q}, k = {self.k}, block width m = {self.m}",
            f"carry states = {self.carry_graph.states}",
            f"remainder states = {self.remainder_graph.states}",
            f"carry graph classes = {self.minimized_carry_graph.class_count}",
            f"remainder graph classes = {self.minimized_remainder_graph.class_count}",
            *self.decision_report.summary_lines(),
            f"implemented statement: {self.implemented_statement}",
            f"open boundary: {self.open_claim_boundary}",
            f"theorem target: {self.decision_report.theorem_target}",
            f"refutation target: {self.decision_report.refutation_target}",
            f"weaker replacement: {self.decision_report.weaker_replacement}",
        )


@dataclass(frozen=True)
class CarryWindowExample:
    """Bridge between raw coefficients, carry states, and long-division blocks."""

    n: int
    base: int
    m: int
    B: int
    q: int
    k: int
    lookahead_blocks: int
    raw_coefficients: tuple[int, ...]
    carried_blocks: tuple[str, ...]
    actual_blocks: tuple[str, ...]
    run: CarryRun

    @property
    def matches_long_division(self) -> bool:
        return self.carried_blocks == self.actual_blocks


@dataclass(frozen=True)
class CarryDFACase:
    """Named carry/DFA comparison used in docs, tests, and datasets."""

    label: str
    comparison: CarryRemainderComparison
    distinctive_feature: str

    @property
    def n(self) -> int:
        return self.comparison.n

    @property
    def factorization_status(self) -> tuple[str, str]:
        return (
            self.comparison.implemented_statement,
            self.comparison.open_claim_boundary,
        )


class CarryTransducer:
    """Finite-window carry machine for base-B blocks."""

    def __init__(self, block_base: int):
        if block_base <= 1:
            raise ValueError("block_base must exceed 1")
        self.block_base = block_base

    def step(self, coefficient: int, carry_in: int, *, is_leftmost: bool) -> tuple[int, int]:
        """
        Advance the carry machine one block to the left.

        The leftmost block keeps any remaining overflow inside the window,
        matching the finite-width normalization used elsewhere in the repo.
        """
        total = coefficient + carry_in
        if is_leftmost:
            return total, 0
        return total % self.block_base, total // self.block_base

    def run(self, coefficients: list[int]) -> CarryRun:
        """
        Normalize coefficients listed from most to least significant block.
        """
        transitions_rev = []
        carry = 0
        for offset, coefficient in enumerate(reversed(coefficients)):
            position = len(coefficients) - 1 - offset
            block_value, carry_out = self.step(
                coefficient,
                carry,
                is_leftmost=(position == 0),
            )
            transitions_rev.append(
                CarryTransition(
                    position=position,
                    coefficient=coefficient,
                    carry_in=carry,
                    block_value=block_value,
                    carry_out=carry_out,
                )
            )
            carry = carry_out
        return CarryRun(self.block_base, tuple(reversed(transitions_rev)))

    def summarize(self, coefficients: list[int]) -> CarryStateSummary:
        return self.run(coefficients).state_summary()

    def export_dot(self, coefficients: list[int]) -> str:
        return self.summarize(coefficients).to_dot()

    def graph(self, coefficients: list[int]) -> StateGraph:
        return self.summarize(coefficients).graph()

    def minimize(self, coefficients: list[int]) -> MinimizedStateGraph:
        return self.graph(coefficients).minimize()


def remainder_dfa_run(
    n: int,
    *,
    block_base: int,
    steps: int,
) -> RemainderRun:
    """Run the long-division DFA for `steps` block transitions."""
    transitions: list[RemainderTransition] = []
    remainder = 1
    for position in range(steps):
        total = block_base * remainder
        block_value = total // n
        remainder_out = total % n
        transitions.append(
            RemainderTransition(
                position=position,
                remainder_in=remainder,
                block_value=block_value,
                remainder_out=remainder_out,
            )
        )
        remainder = remainder_out
    return RemainderRun(modulus=n, block_base=block_base, transitions=tuple(transitions))


def carry_window_example(
    n: int,
    *,
    base: int = 10,
    n_blocks: int = 12,
    prefer_m: int | None = None,
    max_lookahead_blocks: int = 128,
) -> CarryWindowExample:
    """
    Build the three-layer view for one example:

    raw coefficients qk^j -> carry transducer -> displayed long-division blocks.
    """
    comparison = skeleton_vs_actual(n, base=base, n_blocks=n_blocks, prefer_m=prefer_m)
    if comparison.get("terminates"):
        raise ValueError(f"1/{n} terminates in base {base}; no carried-prefix visibility window exists")
    carried_blocks = tuple(comparison["carried"])
    run = CarryTransducer(comparison["B"]).run(comparison["raw"])
    lookahead_blocks = 0

    if carried_blocks != tuple(comparison["actual"]):
        for extra in range(1, max_lookahead_blocks + 1):
            raw = raw_series_blocks(comparison["q"], comparison["k"], n_blocks + extra)
            run = CarryTransducer(comparison["B"]).run(raw)
            carried_blocks = tuple(run.render(comparison["m"])[:n_blocks])
            if carried_blocks == tuple(comparison["actual"]):
                lookahead_blocks = extra
                break
        else:
            raise ValueError(
                f"carry prefix for 1/{n} did not stabilize within {max_lookahead_blocks} lookahead block(s)"
            )
    else:
        carried_blocks = tuple(apply_carry(comparison["raw"], comparison["B"]))

    return CarryWindowExample(
        n=n,
        base=base,
        m=comparison["m"],
        B=comparison["B"],
        q=comparison["q"],
        k=comparison["k"],
        lookahead_blocks=lookahead_blocks,
        raw_coefficients=tuple(run_transition.coefficient for run_transition in run.transitions),
        carried_blocks=carried_blocks,
        actual_blocks=tuple(comparison["actual"]),
        run=run,
    )


def carry_remainder_comparison(
    n: int,
    *,
    base: int = 10,
    n_blocks: int = 12,
    prefer_m: int | None = None,
    max_lookahead_blocks: int = 128,
) -> CarryRemainderComparison:
    """
    Compare the finite-window carry transducer to the long-division DFA.

    This packages the currently implemented statement: both machines produce the
    same displayed block word on the visible window. It does not assert a
    canonical global factorization theorem.
    """
    example = carry_window_example(
        n,
        base=base,
        n_blocks=n_blocks,
        prefer_m=prefer_m,
        max_lookahead_blocks=max_lookahead_blocks,
    )
    remainder_run = remainder_dfa_run(n, block_base=example.B, steps=n_blocks)
    alignments = tuple(
        StateAlignment(
            position=carry_transition.position,
            coefficient=carry_transition.coefficient,
            carry_state=carry_transition.carry_in,
            remainder_state=remainder_transition.remainder_in,
            block_value=carry_transition.block_value,
        )
        for carry_transition, remainder_transition in zip(
            example.run.transitions,
            remainder_run.transitions,
        )
    )
    return CarryRemainderComparison(
        n=n,
        base=base,
        m=example.m,
        B=example.B,
        q=example.q,
        k=example.k,
        lookahead_blocks=example.lookahead_blocks,
        carry_example=example,
        remainder_run=remainder_run,
        alignments=alignments,
    )


def canonical_carry_dfa_examples(base: int = 10) -> tuple[CarryDFACase, ...]:
    """
    Return the canonical carry/DFA comparisons used throughout the repo.

    The comparisons expose the currently implemented finite-window agreement
    while keeping the canonical global factorization claim explicitly open.
    """
    examples = [
        (
            "Trivial state relabeling",
            21,
            6,
            "in this block coordinate both observed finite-window functional criteria hold and both machines collapse to one state, giving the trivial relabeling regime",
        ),
        (
            "Prime carry interaction",
            97,
            2,
            "finite-window outputs match, the observed remainder-to-carry functional criterion holds, and the carry-to-remainder criterion fails, so the window is quotient-only rather than a relabeling",
        ),
        (
            "Composite preperiod plus carry",
            996,
            3,
            "the same quotient-only finite-window regime persists in a composite example with preperiod and same-core structure",
        ),
    ]
    return tuple(
        CarryDFACase(
            label=label,
            comparison=carry_remainder_comparison(
                n,
                base=base,
                n_blocks=8,
                prefer_m=prefer_m,
            ),
            distinctive_feature=distinctive_feature,
        )
        for label, n, prefer_m, distinctive_feature in examples
    )


def canonical_carry_selector_case_studies(base: int = 10) -> tuple[CarrySelectorCaseStudy, ...]:
    """Canonical selector-profile case studies for Track 17."""
    if base != 10:
        return ()
    cases = [
        (
            "Isolated k = 1 relabeling window",
            21,
            "The selector profile finite_word_only -> state_relabeling -> finite_word_only shows that trivial relabeling can appear only at one isolated block width.",
        ),
        (
            "Isolated non-k = 1 relabeling window",
            249,
            "This is the cleanest decimal example where the selector chooses a genuine non-k = 1 relabeling window, at m = 6 with k = 16.",
        ),
        (
            "Same-core quotient-only persistence",
            996,
            "The same-core denominator 996 never reaches a relabeling window on the tested profile, even though 249 does.",
        ),
    ]
    studies: list[CarrySelectorCaseStudy] = []
    for label, n, explanation in cases:
        profile = carry_factorization_selector_profile(n, base=base, n_blocks=8, max_m=8)
        studies.append(
            CarrySelectorCaseStudy(
                label=label,
                n=n,
                base=base,
                explanation=explanation,
                theorem_candidate="Classify when selector profiles admit isolated or repeated state-relabeling windows beyond the trivial k = 1 coordinates.",
                heuristic_note="Selector profiles appear to capture stable family behavior rather than just finding the smallest residue coordinate.",
                counterexample_target="Use this case to test naive claims that larger block widths, stripped cores, or output agreement alone determine the state-level regime.",
                primary_vocabulary_id="carry_layer",
                profile=profile,
            )
        )
    return tuple(studies)


def canonical_carry_selector_family_studies(base: int = 10) -> tuple[CarrySelectorFamilyStudy, ...]:
    """Canonical selector-profile family studies for Track 17."""
    if base != 10:
        return ()
    same_core = compare_carry_selector_profiles(249, 996, base=base, n_blocks=8, max_m=8)
    doubling = compare_carry_selector_profiles(17, 34, base=base, n_blocks=8, max_m=8)
    profile_249 = carry_factorization_selector_profile(249, base=base, n_blocks=8, max_m=8)
    profile_498 = carry_factorization_selector_profile(498, base=base, n_blocks=8, max_m=8)
    profile_996 = carry_factorization_selector_profile(996, base=base, n_blocks=8, max_m=8)
    return (
        CarrySelectorFamilyStudy(
            label="Non-k = 1 relabeling windows",
            members=(17, 19, 29, 249),
            explanation="State-relabeling is not confined to k = 1 coordinates. The selector isolates nontrivial relabeling windows at examples like 17, 19, 29, and 249 in base 10.",
            theorem_candidate="Determine arithmetic criteria for non-k = 1 selector windows where the observed carry and remainder states become bijective on the visible trace.",
            heuristic_note="Non-k = 1 relabeling windows appear sparse and often isolated in m, which makes them plausible theorem targets rather than random noise.",
            counterexample_target="Refute any claim that state relabeling can only occur at trivial constant-coefficient or repunit-style coordinates.",
            primary_vocabulary_id="carry_layer",
            summary_lines=tuple(
                line
                for n in (17, 19, 29, 249)
                for line in (
                    f"N = {n}",
                    *carry_factorization_selector_profile(n, base=base, n_blocks=8, max_m=8).selector_summary_lines,
                    "---",
                )
            )[:-1],
        ),
        CarrySelectorFamilyStudy(
            label="Same-core relabeling loss",
            members=(249, 498, 996),
            explanation="The selector profile is not determined by stripped periodic core. Core 249 supports an isolated relabeling window, while same-core 498 and 996 stay quotient-only.",
            theorem_candidate="Classify which same-core deformations preserve, shift, or destroy relabeling windows.",
            heuristic_note="The selector profile depends on the actual denominator, not just the periodic core and not just the visible output word.",
            counterexample_target="Use same-core families to reject any theorem candidate that ignores actual-denominator effects once the periodic core is fixed.",
            primary_vocabulary_id="remainder_orbit",
            summary_lines=same_core.summary_lines()
            + ("---",)
            + (
                f"249 selector signature = {profile_249.transition_signature}, relabeling modes = {profile_249.relabeling_modes}",
                f"498 selector signature = {profile_498.transition_signature}, relabeling modes = {profile_498.relabeling_modes}",
                f"996 selector signature = {profile_996.transition_signature}, relabeling modes = {profile_996.relabeling_modes}",
            ),
        ),
        CarrySelectorFamilyStudy(
            label="Small-multiple relabeling shift and enlargement",
            members=(17, 34, 68),
            explanation="Small-multiple moves can preserve and enlarge relabeling windows rather than merely shifting or destroying them: 17 relabels at m = 5, 34 relabels at m = 5 and 7, and 68 loses relabeling entirely.",
            theorem_candidate="Describe how multiplying by stripped base factors changes selector signatures and relabeling-mode sets.",
            heuristic_note="Selector profiles behave like family objects under small multiples, not like single-coordinate accidents.",
            counterexample_target="Reject any monotonicity rule that predicts relabeling windows only move in one direction or can only disappear.",
            primary_vocabulary_id="carry_layer",
            summary_lines=doubling.summary_lines()
            + ("---",)
            + carry_factorization_selector_profile(68, base=base, n_blocks=8, max_m=8).selector_summary_lines,
        ),
    )


def _selected_factorization_comparison(
    n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_m: int = 12,
    max_block_base: int = 10_000_000,
) -> tuple[CarryFactorizationSelectorProfile, CarryRemainderComparison]:
    """Return the selected Track 17 profile step together with its comparison."""
    profile = carry_factorization_selector_profile(
        n,
        base=base,
        n_blocks=n_blocks,
        max_m=max_m,
        max_block_base=max_block_base,
    )
    prefer_m = profile.selected_m
    if prefer_m is None:
        raise ValueError(f"no selected factorization coordinate for 1/{n} in base {base}")
    comparison = carry_remainder_comparison(
        n,
        base=base,
        n_blocks=n_blocks,
        prefer_m=prefer_m,
    )
    return profile, comparison


def _state_merging_row(
    comparison: CarryRemainderComparison,
    *,
    profile: CarryFactorizationSelectorProfile,
) -> dict[str, object]:
    report = comparison.decision_report
    forward = report.remainder_to_carry_map
    reverse = report.carry_to_remainder_map
    return {
        "n": comparison.n,
        "base": comparison.base,
        "m": comparison.m,
        "B": comparison.B,
        "q": comparison.q,
        "k": comparison.k,
        "factorization_regime": report.regime,
        "obstruction_class": report.obstruction_class,
        "obstruction_summary": report.obstruction_summary,
        "profile_class": carry_selector_profile_class(profile),
        "transition_signature": list(profile.transition_signature),
        "relabeling_modes": list(profile.relabeling_modes),
        "quotient_modes": list(profile.quotient_modes),
        "finite_word_only_modes": list(profile.finite_word_only_modes),
        "has_isolated_relabeling_window": profile.has_isolated_relabeling_window,
        "carry_state_count": report.carry_state_count,
        "remainder_state_count": report.remainder_state_count,
        "carry_class_count": report.carry_class_count,
        "remainder_class_count": report.remainder_class_count,
        "graph_state_gap": report.graph_state_gap,
        "minimized_class_gap": report.minimized_class_gap,
        "observed_alignment_bijection": report.observed_alignment_bijection,
        "state_relabeling_candidate": report.state_relabeling_candidate,
        "remainder_to_carry_quotient_candidate": report.remainder_to_carry_quotient_candidate,
        "carry_to_remainder_lift_candidate": report.carry_to_remainder_lift_candidate,
        "forward_profile": forward.export(),
        "reverse_profile": reverse.export(),
        "compression_targets": [
            {
                "target_state": target,
                "source_states": list(sources),
                "preimage_size": len(sources),
            }
            for target, sources in report.compression_targets
        ],
        "forward_preimage_signature": forward.preimage_signature,
        "reverse_preimage_signature": reverse.preimage_signature,
        "forward_ambiguity_signature": forward.ambiguity_signature,
        "reverse_ambiguity_signature": reverse.ambiguity_signature,
        "alignment_rows": list(comparison.alignment_rows),
        **claim_context_for_parameters(
            ("carry_window_transducer", "carry_dfa_factorization"),
            base=comparison.base,
            n=comparison.n,
        ),
    }


def canonical_state_merging_case_studies(base: int = 10) -> tuple[StateMergingCaseStudy, ...]:
    """Canonical preimage-fiber profile case studies on the selected Track 17 coordinate."""
    if base != 10:
        return ()
    cases = [
        (
            "One-state relabeling",
            21,
            "The carry layer collapses completely here: the selected window is a genuine one-state relabeling, so the preimage-fiber profile is bijective in both directions.",
            "Describe when the selected coordinate gives a true finite-window relabeling rather than a one-way quotient.",
            "This is the degenerate baseline where no state compression remains after normalization.",
            "Use `21` to keep the fully symmetric case visible before reading quotient-only examples as the default.",
            "carry_layer",
        ),
        (
            "Visible prime compression",
            97,
            "The selected decimal window keeps a functional remainder-to-carry map, but several remainder states collapse onto carry state `0`, so the reverse direction already fails.",
            "Measure how much orbit information survives the projection from remainder states to carry states on selected prime windows.",
            "This is the cleanest prime example where visible output agreement coexists with genuine state compression.",
            "Use `97` to reject any naive claim that output agreement plus prime periodicity forces a state relabeling.",
            "remainder_orbit",
        ),
        (
            "Hidden prime obstruction",
            89,
            "The aligned window is bijective in both directions, but the carry graph and the remainder graph still have different observed sizes, so the obstruction hides in graph structure rather than visible compression.",
            "Describe which quotient-only cases remain collision-free on the aligned window and only fail at the graph layer.",
            "This is the cleanest prime example where the finite preimage-fiber surface stays bijective even though relabeling still fails.",
            "Use `89` to keep the hidden graph obstruction visible beside the more obvious compression cases.",
            "remainder_orbit",
        ),
        (
            "Visible composite compression",
            996,
            "The same forward-only compression persists in a composite example with preperiod and same-core structure, so quotient-only behavior is not a prime-specific accident.",
            "Characterize which preperiod/composite deformations preserve quotient-only state compression on the selected window.",
            "This keeps the same-core frontier adjacent to the canonical quotient-only profile.",
            "Use `996` to reject any theorem candidate that attributes quotient-only collapse solely to prime or purely periodic structure.",
            "remainder_orbit",
        ),
    ]
    studies: list[StateMergingCaseStudy] = []
    for label, n, explanation, theorem_candidate, heuristic_note, counterexample_target, vocabulary_id in cases:
        profile, comparison = _selected_factorization_comparison(
            n,
            base=base,
            n_blocks=8,
            max_m=8,
        )
        studies.append(
            StateMergingCaseStudy(
                label=label,
                n=n,
                base=base,
                explanation=explanation,
                theorem_candidate=theorem_candidate,
                heuristic_note=heuristic_note,
                counterexample_target=counterexample_target,
                primary_vocabulary_id=vocabulary_id,
                profile=profile,
                comparison=comparison,
            )
        )
    return tuple(studies)


def canonical_state_merging_family_studies(base: int = 10) -> tuple[StateMergingFamilyStudy, ...]:
    """Canonical family studies for the preimage-fiber profile surface."""
    if base != 10:
        return ()
    family_specs = [
        (
            "Same-core visible compression",
            (249, 498, 996),
            "The stripped periodic core does not determine the finite-window compression pattern: `249` reaches a bijective selected window, while same-core `498` and `996` stay quotient-only with visible reverse collapse.",
            "Classify which same-core deformations preserve, shift, or destroy finite-window state compression signatures.",
            "The preimage-fiber profile depends on the actual denominator, not only on the periodic core or the emitted blocks.",
            "Use this family to reject any factorization frontier that treats same-core data as sufficient for the state-compression story.",
            "remainder_orbit",
        ),
        (
            "Mixed obstruction family",
            (17, 34, 68, 85),
            "This same-core family spans all three selected-coordinate outcomes in one place: `17` and `34` keep relabeling windows, `68` becomes a hidden graph obstruction, and `85` shows visible compression.",
            "Describe how multiplying by base-supported factors changes the selected preimage-fiber profile and can move a family from relabeling to hidden obstruction to visible compression.",
            "This family shows that quotient-only behavior is not one thing: some failures are visible in the fibers, while others only appear at the graph layer.",
            "Use `17 / 34 / 68 / 85` to reject any classifier that treats every quotient-only case as the same kind of obstruction.",
            "carry_layer",
        ),
    ]
    studies: list[StateMergingFamilyStudy] = []
    for label, members, explanation, theorem_candidate, heuristic_note, counterexample_target, vocabulary_id in family_specs:
        member_cases_list: list[StateMergingCaseStudy] = []
        for n in members:
            profile, comparison = _selected_factorization_comparison(
                n,
                base=base,
                n_blocks=8,
                max_m=8,
            )
            member_cases_list.append(
                StateMergingCaseStudy(
                    label=f"1/{n}",
                    n=n,
                    base=base,
                    explanation="Selected-coordinate preimage-fiber profile inside the canonical family study.",
                    theorem_candidate=theorem_candidate,
                    heuristic_note=heuristic_note,
                    counterexample_target=counterexample_target,
                    primary_vocabulary_id=vocabulary_id,
                    profile=profile,
                    comparison=comparison,
                )
            )
        member_cases = tuple(member_cases_list)
        studies.append(
            StateMergingFamilyStudy(
                label=label,
                members=members,
                explanation=explanation,
                theorem_candidate=theorem_candidate,
                heuristic_note=heuristic_note,
                counterexample_target=counterexample_target,
                primary_vocabulary_id=vocabulary_id,
                member_cases=member_cases,
                summary_lines=tuple(
                    line
                    for case in member_cases
                    for line in (
                        (
                            f"N = {case.n}, regime = {case.comparison.decision_report.regime}, "
                            f"obstruction = {case.comparison.decision_report.obstruction_class}, "
                            f"selected m = {case.profile.selected_m}"
                        ),
                        f"forward preimage signature = {case.comparison.remainder_to_carry_map.preimage_signature}",
                        f"reverse ambiguity signature = {case.comparison.carry_to_remainder_map.ambiguity_signature}",
                        "---",
                    )
                )[:-1],
            )
        )
    return tuple(studies)


def state_merging_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_block_base: int = 10_000_000,
    max_m: int = 12,
) -> list[dict[str, object]]:
    """Export selected-coordinate preimage-fiber profiles for bounded search."""
    rows: list[dict[str, object]] = []
    for n in range(2, max_n + 1):
        try:
            profile, comparison = _selected_factorization_comparison(
                n,
                base=base,
                n_blocks=n_blocks,
                max_m=max_m,
                max_block_base=max_block_base,
            )
        except Exception:
            continue
        if comparison.B > max_block_base or comparison.q <= 0:
            continue
        rows.append(_state_merging_row(comparison, profile=profile))
    regime_priority = {
        "state_relabeling": 0,
        "quotient_candidate_only": 1,
        "finite_word_only": 2,
    }
    rows.sort(
        key=lambda row: (
            regime_priority[str(row["factorization_regime"])],
            {
                "state_relabeling": 0,
                "visible_preimage_compression": 1,
                "hidden_graph_obstruction": 2,
                "finite_word_only": 3,
            }[str(row["obstruction_class"])],
            -int(row["forward_profile"]["max_preimage_size"]),
            int(row["k"]),
            int(row["n"]),
        )
    )
    return rows


def _compress_adjacent_labels(labels: list[str]) -> list[str]:
    """Compress a label path by removing consecutive duplicates."""
    compressed: list[str] = []
    for label in labels:
        if not compressed or compressed[-1] != label:
            compressed.append(label)
    return compressed


def _same_core_obstruction_phase_fields(
    member_ids: list[int],
    selected_obstruction_classes: list[str],
) -> dict[str, object]:
    """Derive phase and switching data for a same-core selected-coordinate family."""
    relabeling_members = [
        member
        for member, obstruction_class in zip(member_ids, selected_obstruction_classes)
        if obstruction_class == "state_relabeling"
    ]
    hidden_members = [
        member
        for member, obstruction_class in zip(member_ids, selected_obstruction_classes)
        if obstruction_class == "hidden_graph_obstruction"
    ]
    visible_members = [
        member
        for member, obstruction_class in zip(member_ids, selected_obstruction_classes)
        if obstruction_class == "visible_preimage_compression"
    ]
    def _multiplier_v2_v5(member: int | None) -> tuple[int | None, int | None]:
        if member is None:
            return (None, None)
        multiplier = member // member_ids[0]
        v2 = 0
        while multiplier % 2 == 0:
            multiplier //= 2
            v2 += 1
        v5 = 0
        while multiplier % 5 == 0:
            multiplier //= 5
            v5 += 1
        return (v2, v5)

    compressed_class_path = _compress_adjacent_labels(selected_obstruction_classes)
    obstruction_only_path = [
        obstruction_class
        for obstruction_class in selected_obstruction_classes
        if obstruction_class in {"hidden_graph_obstruction", "visible_preimage_compression"}
    ]
    compressed_obstruction_path = _compress_adjacent_labels(obstruction_only_path)
    hidden_visible_switch_count = max(len(compressed_obstruction_path) - 1, 0)
    first_relabeling_member = relabeling_members[0] if relabeling_members else None
    first_non_relabeling_member = next(
        (member for member, obstruction_class in zip(member_ids, selected_obstruction_classes) if obstruction_class != "state_relabeling"),
        None,
    )
    first_hidden_member = hidden_members[0] if hidden_members else None
    first_visible_member = visible_members[0] if visible_members else None
    has_visible_after_hidden = bool(
        first_hidden_member is not None
        and any(member > first_hidden_member for member in visible_members)
    )
    has_rehidden_after_visible = bool(
        first_visible_member is not None
        and any(member > first_visible_member for member in hidden_members)
    )
    has_nonmonotone_hidden_visible_switching = hidden_visible_switch_count >= 2
    if first_visible_member is None:
        visibility_behavior = "hidden_only"
        onset_kind = "hidden_only"
    elif first_hidden_member is None:
        visibility_behavior = "one_way_visible"
        onset_kind = "visible_without_hidden"
    elif first_visible_member < first_hidden_member:
        visibility_behavior = "rehiding_visible" if has_rehidden_after_visible else "one_way_visible"
        onset_kind = "visible_first"
    elif first_hidden_member < first_visible_member:
        visibility_behavior = "rehiding_visible" if has_rehidden_after_visible else "one_way_visible"
        onset_kind = "hidden_first"
    else:
        visibility_behavior = "rehiding_visible" if has_rehidden_after_visible else "one_way_visible"
        onset_kind = "same_step"
    first_visible_multiplier_v2, first_visible_multiplier_v5 = _multiplier_v2_v5(first_visible_member)
    first_hidden_multiplier_v2, first_hidden_multiplier_v5 = _multiplier_v2_v5(first_hidden_member)
    class_path_text = " -> ".join(compressed_class_path) if compressed_class_path else "none"
    if has_nonmonotone_hidden_visible_switching:
        phase_summary = (
            f"same-core path {class_path_text} with {hidden_visible_switch_count} hidden/visible switches"
        )
    elif has_rehidden_after_visible:
        phase_summary = f"same-core path {class_path_text} re-hides after visible compression appears"
    elif has_visible_after_hidden:
        phase_summary = f"same-core path {class_path_text} becomes visible after an earlier hidden phase"
    elif first_visible_member is not None:
        phase_summary = f"same-core path {class_path_text} reaches visible compression without later re-hiding"
    elif first_hidden_member is not None:
        phase_summary = f"same-core path {class_path_text} stays hidden once the family leaves relabeling"
    else:
        phase_summary = f"same-core path {class_path_text}"
    return {
        "relabeling_members": relabeling_members,
        "hidden_members": hidden_members,
        "visible_members": visible_members,
        "compressed_class_path": compressed_class_path,
        "compressed_obstruction_path": compressed_obstruction_path,
        "first_relabeling_member": first_relabeling_member,
        "first_non_relabeling_member": first_non_relabeling_member,
        "first_hidden_member": first_hidden_member,
        "first_visible_member": first_visible_member,
        "first_visible_multiplier_v2": first_visible_multiplier_v2,
        "first_visible_multiplier_v5": first_visible_multiplier_v5,
        "first_hidden_multiplier_v2": first_hidden_multiplier_v2,
        "first_hidden_multiplier_v5": first_hidden_multiplier_v5,
        "visibility_behavior": visibility_behavior,
        "onset_kind": onset_kind,
        "has_visible_after_hidden": has_visible_after_hidden,
        "has_rehidden_after_visible": has_rehidden_after_visible,
        "has_nonmonotone_hidden_visible_switching": has_nonmonotone_hidden_visible_switching,
        "hidden_visible_switch_count": hidden_visible_switch_count,
        "phase_summary": phase_summary,
    }


def state_merging_same_core_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_block_base: int = 10_000_000,
    max_m: int = 12,
    require_disagreement: bool = True,
) -> list[dict[str, object]]:
    """Group selected-coordinate preimage-fiber profiles by stripped periodic core."""
    grouped: dict[int, list[dict[str, object]]] = {}
    for row in state_merging_rows(
        max_n,
        base=base,
        n_blocks=n_blocks,
        max_block_base=max_block_base,
        max_m=max_m,
    ):
        core, _ = strip_base_factors(int(row["n"]), base)
        if core == 1:
            continue
        grouped.setdefault(core, []).append(row)

    rows: list[dict[str, object]] = []
    for core, members in grouped.items():
        if len(members) < 2:
            continue
        members.sort(key=lambda row: int(row["n"]))
        member_ids = [int(row["n"]) for row in members]
        selected_regimes = [str(row["factorization_regime"]) for row in members]
        selected_obstruction_classes = [str(row["obstruction_class"]) for row in members]
        forward_signatures = [str(row["forward_preimage_signature"]) for row in members]
        reverse_ambiguity_signatures = [str(row["reverse_ambiguity_signature"]) for row in members]
        has_disagreement = (
            len(set(selected_regimes)) > 1
            or len(set(selected_obstruction_classes)) > 1
            or len(set(forward_signatures)) > 1
            or len(set(reverse_ambiguity_signatures)) > 1
        )
        if require_disagreement and not has_disagreement:
            continue
        class_set = set(selected_obstruction_classes)
        row = {
            "core_n": core,
            "base": base,
            "members": member_ids,
            "selected_members": member_ids,
            "selected_regimes": selected_regimes,
            "selected_obstruction_classes": selected_obstruction_classes,
            "forward_preimage_signatures": forward_signatures,
            "reverse_ambiguity_signatures": reverse_ambiguity_signatures,
            "has_regime_disagreement": len(set(selected_regimes)) > 1,
            "has_obstruction_class_disagreement": len(class_set) > 1,
            "has_forward_preimage_disagreement": len(set(forward_signatures)) > 1,
            "has_reverse_ambiguity_disagreement": len(set(reverse_ambiguity_signatures)) > 1,
            "has_hidden_graph_obstruction_member": "hidden_graph_obstruction" in class_set,
            "has_visible_preimage_compression_member": "visible_preimage_compression" in class_set,
            "crosses_relabeling_hidden_visible_classes": {
                "state_relabeling",
                "hidden_graph_obstruction",
                "visible_preimage_compression",
            }.issubset(class_set),
            "has_state_merging_disagreement": has_disagreement,
            **_same_core_obstruction_phase_fields(member_ids, selected_obstruction_classes),
            **claim_context_for_parameters(
                ("carry_window_transducer", "carry_dfa_factorization"),
                base=base,
                actual=member_ids[-1],
                core=core,
                requested_blocks=n_blocks,
            ),
        }
        rows.append(row)
    rows.sort(
        key=lambda row: (
            not bool(row["has_nonmonotone_hidden_visible_switching"]),
            not bool(row["crosses_relabeling_hidden_visible_classes"]),
            not bool(row["has_state_merging_disagreement"]),
            int(row["core_n"]),
        )
    )
    return rows


def quotient_obstruction_census_from_rows(
    rows: list[dict[str, object]],
    *,
    base: int,
    max_n: int,
    n_blocks: int,
) -> dict[str, object]:
    """Summarize visible vs hidden quotient-only obstructions from selected-coordinate rows."""
    quotient_rows = [row for row in rows if str(row["factorization_regime"]) == "quotient_candidate_only"]
    visible_rows = [
        row for row in quotient_rows
        if str(row["obstruction_class"]) == "visible_preimage_compression"
    ]
    hidden_rows = [
        row for row in quotient_rows
        if str(row["obstruction_class"]) == "hidden_graph_obstruction"
    ]
    return {
        "group": "census_summary",
        "base": base,
        "max_n": max_n,
        "n_blocks": n_blocks,
        "quotient_candidate_only_count": len(quotient_rows),
        "visible_preimage_compression_count": len(visible_rows),
        "hidden_graph_obstruction_count": len(hidden_rows),
        "representative_visible_ns": [int(row["n"]) for row in visible_rows[:5]],
        "representative_hidden_ns": [int(row["n"]) for row in hidden_rows[:5]],
        "decision": (
            "Selected-coordinate quotient-only cases separate into visible preimage compression "
            "and hidden graph obstruction beneath the open `carry_dfa_factorization` boundary."
        ),
        "summary_lines": [
            f"quotient-only count = {len(quotient_rows)}",
            f"visible preimage compression count = {len(visible_rows)}",
            f"hidden graph obstruction count = {len(hidden_rows)}",
        ],
        **claim_context_for_parameters(
            ("carry_window_transducer", "carry_dfa_factorization"),
            base=base,
            requested_blocks=n_blocks,
        ),
    }


def quotient_obstruction_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_block_base: int = 10_000_000,
    max_m: int = 12,
) -> list[dict[str, object]]:
    """Group visible and hidden quotient-only cases on the selected Track 17 coordinate."""
    visible_priority = {97: 0, 996: 1}
    hidden_priority = {89: 0, 68: 1, 34: 2}

    rows = state_merging_rows(
        max_n,
        base=base,
        n_blocks=n_blocks,
        max_block_base=max_block_base,
        max_m=max_m,
    )
    quotient_rows = [
        row for row in rows
        if str(row["factorization_regime"]) == "quotient_candidate_only"
    ]
    visible_rows = [
        {"group": "visible_preimage_compression", **row}
        for row in quotient_rows
        if str(row["obstruction_class"]) == "visible_preimage_compression"
    ]
    hidden_rows = [
        {"group": "hidden_graph_obstruction", **row}
        for row in quotient_rows
        if str(row["obstruction_class"]) == "hidden_graph_obstruction"
    ]
    visible_rows.sort(
        key=lambda row: (
            visible_priority.get(int(row["n"]), len(visible_priority)),
            -int(row["forward_profile"]["max_preimage_size"]),
            int(row["k"]),
            int(row["n"]),
        )
    )
    hidden_rows.sort(
        key=lambda row: (
            hidden_priority.get(int(row["n"]), len(hidden_priority)),
            -abs(int(row["graph_state_gap"])),
            -abs(int(row["minimized_class_gap"])),
            int(row["k"]),
            int(row["n"]),
        )
    )
    featured_visible_rows = visible_rows[:5]
    featured_hidden_rows = hidden_rows[:5]
    remaining_visible_rows = visible_rows[5:]
    remaining_hidden_rows = hidden_rows[5:]
    return [
        quotient_obstruction_census_from_rows(
            rows,
            base=base,
            max_n=max_n,
            n_blocks=n_blocks,
        ),
        *featured_visible_rows,
        *featured_hidden_rows,
        *remaining_visible_rows,
        *remaining_hidden_rows,
    ]


def quotient_obstruction_family_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_block_base: int = 10_000_000,
    max_m: int = 12,
    require_disagreement: bool = True,
) -> list[dict[str, object]]:
    """Group same-core families by visible/hidden obstruction class on selected coordinates."""
    family_priority = {17: 0, 249: 1}
    rows = state_merging_same_core_rows(
        max_n,
        base=base,
        n_blocks=n_blocks,
        max_block_base=max_block_base,
        max_m=max_m,
        require_disagreement=require_disagreement,
    )
    filtered = [
        row
        for row in rows
        if {"visible_preimage_compression", "hidden_graph_obstruction"} & set(row["selected_obstruction_classes"])
    ]
    filtered.sort(
        key=lambda row: (
            family_priority.get(int(row["core_n"]), len(family_priority)),
            not bool(row["crosses_relabeling_hidden_visible_classes"]),
            not bool(row["has_obstruction_class_disagreement"]),
            int(row["core_n"]),
        )
    )
    return filtered


def same_core_obstruction_phase_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_block_base: int = 10_000_000,
    max_m: int = 12,
    require_obstruction_members: bool = True,
) -> list[dict[str, object]]:
    """Export same-core family rows ordered by visible/hidden obstruction-phase signal."""
    family_priority = {17: 0, 29: 1, 49: 2, 249: 3}
    rows = state_merging_same_core_rows(
        max_n,
        base=base,
        n_blocks=n_blocks,
        max_block_base=max_block_base,
        max_m=max_m,
        require_disagreement=False,
    )
    if require_obstruction_members:
        rows = [
            row
            for row in rows
            if bool(row["has_hidden_graph_obstruction_member"]) or bool(row["has_visible_preimage_compression_member"])
        ]
    rows.sort(
        key=lambda row: (
            family_priority.get(int(row["core_n"]), len(family_priority)),
            not bool(row["has_nonmonotone_hidden_visible_switching"]),
            -int(row["hidden_visible_switch_count"]),
            not bool(row["has_rehidden_after_visible"]),
            not bool(row["crosses_relabeling_hidden_visible_classes"]),
            int(row["first_visible_member"] or 10**9),
            int(row["core_n"]),
        )
    )
    return rows


def same_core_obstruction_correlate_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_block_base: int = 10_000_000,
    max_m: int = 12,
) -> list[dict[str, object]]:
    """Summarize empirical correlates of re-hiding versus one-way visible same-core families."""
    families = same_core_obstruction_phase_rows(
        max_n,
        base=base,
        n_blocks=n_blocks,
        max_block_base=max_block_base,
        max_m=max_m,
        require_obstruction_members=True,
    )
    visible_families = [row for row in families if row["first_visible_member"] is not None]
    rehiding_families = [row for row in visible_families if row["has_rehidden_after_visible"]]
    one_way_visible_families = [
        row for row in visible_families if not row["has_rehidden_after_visible"]
    ]
    hidden_only_families = [
        row for row in families
        if row["first_visible_member"] is None and row["first_hidden_member"] is not None
    ]

    def _ratio(numerator: int, denominator: int) -> float | None:
        if denominator == 0:
            return None
        return round(numerator / denominator, 3)

    def _onset_kind(row: dict[str, object]) -> str:
        first_visible = row["first_visible_member"]
        first_hidden = row["first_hidden_member"]
        if first_visible is None:
            return "hidden_only"
        if first_hidden is None:
            return "visible_without_hidden"
        if int(first_visible) < int(first_hidden):
            return "visible_first"
        if int(first_hidden) < int(first_visible):
            return "hidden_first"
        return "same_step"

    def _valuation_bucket(v2: int | None, v5: int | None) -> str:
        if v2 is None or v5 is None:
            return "none"
        return f"v2={v2},v5={v5}"

    rows: list[dict[str, object]] = [
        {
            "group": "behavior_census",
            "base": base,
            "max_n": max_n,
            "n_blocks": n_blocks,
            "visible_family_count": len(visible_families),
            "rehiding_visible_count": len(rehiding_families),
            "one_way_visible_count": len(one_way_visible_families),
            "hidden_only_count": len(hidden_only_families),
            "decision": (
                "At the selected bound, same-core visible families split empirically into "
                "one-way visible paths and re-hiding paths; this is a dataset classification, "
                "not a theorem beneath `carry_dfa_factorization`."
            ),
            "summary_lines": [
                f"visible-family count = {len(visible_families)}",
                f"rehiding-visible count = {len(rehiding_families)}",
                f"one-way-visible count = {len(one_way_visible_families)}",
                f"hidden-only count = {len(hidden_only_families)}",
            ],
            **claim_context_for_parameters(
                ("carry_window_transducer", "carry_dfa_factorization"),
                base=base,
                requested_blocks=n_blocks,
            ),
        }
    ]

    onset_priority = {
        "visible_without_hidden": 0,
        "visible_first": 1,
        "hidden_first": 2,
        "same_step": 3,
    }
    onset_groups: dict[str, list[dict[str, object]]] = {}
    for row in visible_families:
        onset_groups.setdefault(_onset_kind(row), []).append(row)
    for onset_kind, bucket_rows in sorted(
        onset_groups.items(),
        key=lambda item: (
            onset_priority.get(item[0], 99),
            -len(item[1]),
            item[0],
        ),
    ):
        rehiding_count = sum(bool(row["has_rehidden_after_visible"]) for row in bucket_rows)
        one_way_count = len(bucket_rows) - rehiding_count
        rows.append(
            {
                "group": "onset_correlation",
                "onset_kind": onset_kind,
                "family_count": len(bucket_rows),
                "rehiding_count": rehiding_count,
                "one_way_visible_count": one_way_count,
                "rehiding_share": _ratio(rehiding_count, len(bucket_rows)),
                "representative_rehiding_cores": [
                    int(row["core_n"]) for row in bucket_rows if row["has_rehidden_after_visible"]
                ][:5],
                "representative_one_way_visible_cores": [
                    int(row["core_n"]) for row in bucket_rows if not row["has_rehidden_after_visible"]
                ][:5],
                "summary": (
                    f"{onset_kind.replace('_', ' ')} families: {rehiding_count} rehiding vs "
                    f"{one_way_count} one-way visible at N <= {max_n}"
                ),
            }
        )

    def _append_multiplier_group(
        *,
        group_name: str,
        v2_key: str,
        v5_key: str,
    ) -> None:
        buckets: dict[str, list[dict[str, object]]] = {}
        for row in visible_families:
            bucket = _valuation_bucket(row[v2_key], row[v5_key])
            buckets.setdefault(bucket, []).append(row)
        for bucket, bucket_rows in sorted(
            buckets.items(),
            key=lambda item: (
                item[0] == "none",
                -len(item[1]),
                item[0],
            ),
        ):
            rehiding_count = sum(bool(row["has_rehidden_after_visible"]) for row in bucket_rows)
            one_way_count = len(bucket_rows) - rehiding_count
            rows.append(
                {
                    "group": group_name,
                    "valuation_bucket": bucket,
                    "family_count": len(bucket_rows),
                    "rehiding_count": rehiding_count,
                    "one_way_visible_count": one_way_count,
                    "rehiding_share": _ratio(rehiding_count, len(bucket_rows)),
                    "representative_rehiding_cores": [
                        int(row["core_n"]) for row in bucket_rows if row["has_rehidden_after_visible"]
                    ][:5],
                    "representative_one_way_visible_cores": [
                        int(row["core_n"]) for row in bucket_rows if not row["has_rehidden_after_visible"]
                    ][:5],
                }
            )

    _append_multiplier_group(
        group_name="first_hidden_multiplier_correlation",
        v2_key="first_hidden_multiplier_v2",
        v5_key="first_hidden_multiplier_v5",
    )
    _append_multiplier_group(
        group_name="first_visible_multiplier_correlation",
        v2_key="first_visible_multiplier_v2",
        v5_key="first_visible_multiplier_v5",
    )

    feature_priority = {17: 0, 29: 1, 49: 2, 167: 3, 249: 4, 523: 5}
    representative_families = sorted(
        visible_families,
        key=lambda row: (
            feature_priority.get(int(row["core_n"]), len(feature_priority)),
            not bool(row["has_rehidden_after_visible"]),
            int(row["core_n"]),
        ),
    )
    rows.extend(
        {
            "group": "family_examples",
            **row,
        }
        for row in representative_families[:8]
    )
    return rows


def carry_factorization_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_block_base: int = 10_000_000,
    max_m: int = 12,
) -> list[dict[str, object]]:
    """Bounded search surface for Track 17 factorization regimes."""
    rows: list[dict[str, object]] = []
    for n in range(2, max_n + 1):
        try:
            profile = carry_factorization_selector_profile(
                n,
                base=base,
                n_blocks=n_blocks,
                max_m=max_m,
                max_block_base=max_block_base,
            )
            prefer_m = profile.selected_m
            if prefer_m is None:
                continue
            comparison = carry_remainder_comparison(
                n,
                base=base,
                n_blocks=n_blocks,
                prefer_m=prefer_m,
            )
        except Exception:
            continue
        if comparison.B > max_block_base or comparison.q <= 0:
            continue
        report = comparison.decision_report
        rows.append(
            {
                "n": comparison.n,
                "base": comparison.base,
                "m": comparison.m,
                "B": comparison.B,
                "q": comparison.q,
                "k": comparison.k,
                "carry_state_count": len(comparison.carry_graph.states),
                "remainder_state_count": len(comparison.remainder_graph.states),
                "carry_class_count": comparison.minimized_carry_graph.class_count,
                "remainder_class_count": comparison.minimized_remainder_graph.class_count,
                "outputs_match": report.outputs_match,
                "state_relabeling_candidate": report.state_relabeling_candidate,
                "remainder_to_carry_quotient_candidate": report.remainder_to_carry_quotient_candidate,
                "carry_to_remainder_lift_candidate": report.carry_to_remainder_lift_candidate,
                "counterexample_to_state_relabeling": report.counterexample_to_state_relabeling,
                "factorization_regime": report.regime,
                "transition_signature": list(profile.transition_signature),
                "relabeling_modes": list(profile.relabeling_modes),
                "quotient_modes": list(profile.quotient_modes),
                "finite_word_only_modes": list(profile.finite_word_only_modes),
                "has_isolated_relabeling_window": profile.has_isolated_relabeling_window,
                **claim_context_for_parameters(
                    ("carry_window_transducer", "carry_dfa_factorization"),
                    base=comparison.base,
                    n=comparison.n,
                ),
            }
        )
    priority = {
        "quotient_candidate_only": 0,
        "finite_word_only": 1,
        "state_relabeling": 2,
    }
    rows.sort(key=lambda row: (priority[str(row["factorization_regime"])], int(row["k"]), int(row["n"])))
    return rows


def _trace_visibility_event(coefficient: int, block_base: int, carry_in: int) -> str:
    if coefficient >= block_base:
        return "local_overflow"
    if carry_in > 0:
        return "incoming_carry_before_overflow"
    return "carry_free_raw"


def orbit_carry_trace_rows(
    members: tuple[int, ...] = (21, 97, 996),
    *,
    base: int = 10,
    n_blocks: int = 8,
    max_block_base: int = 10_000_000,
    max_m: int = 12,
) -> list[dict[str, object]]:
    """
    Experimental trace lens for the orbit-plus-carry thesis.

    This reports aligned finite-window data only: remainder orbit states, raw
    coefficients, carry states, and displayed blocks. It is not a theorem-level
    promotion of the open global `carry_dfa_factorization` claim.
    """
    rows: list[dict[str, object]] = []
    for n in members:
        prefer_m = CANONICAL_ORBIT_CARRY_TRACE_MODES.get(n)
        if prefer_m is None:
            prefer_m = select_carry_factorization_prefer_m(
                n,
                base=base,
                n_blocks=n_blocks,
                max_m=max_m,
                max_block_base=max_block_base,
            )
        if prefer_m is None:
            continue
        try:
            comparison = carry_remainder_comparison(
                n,
                base=base,
                n_blocks=n_blocks,
                prefer_m=prefer_m,
            )
        except Exception:
            continue
        if comparison.B > max_block_base or comparison.q <= 0:
            continue

        periodic_modulus, _ = strip_base_factors(n, base)
        period = (
            multiplicative_order(comparison.B, periodic_modulus)
            if periodic_modulus > 1
            else None
        )
        report = comparison.decision_report
        carry_transitions = comparison.carry_example.run.transitions[:n_blocks]
        remainder_transitions = comparison.remainder_run.transitions[:n_blocks]

        rows.append(
            {
                "group": "case_summary",
                "n": comparison.n,
                "periodic_modulus": periodic_modulus,
                "base": comparison.base,
                "m": comparison.m,
                "B": comparison.B,
                "q": comparison.q,
                "k": comparison.k,
                "period": period,
                "lookahead_blocks": comparison.lookahead_blocks,
                "outputs_match": report.outputs_match,
                "factorization_regime": report.regime,
                "obstruction_class": report.obstruction_class,
                "carry_state_count": len(comparison.carry_graph.states),
                "remainder_state_count": len(comparison.remainder_graph.states),
                "carry_class_count": comparison.minimized_carry_graph.class_count,
                "remainder_class_count": comparison.minimized_remainder_graph.class_count,
                "open_claim_boundary": comparison.open_claim_boundary,
            }
        )

        for carry_transition, remainder_transition, carried_block, actual_block in zip(
            carry_transitions,
            remainder_transitions,
            comparison.carry_example.carried_blocks,
            comparison.carry_example.actual_blocks,
        ):
            cycle_index = carry_transition.position % period if period else None
            coefficient_fits_block = carry_transition.coefficient < comparison.B
            rows.append(
                {
                    "group": "trace_step",
                    "n": comparison.n,
                    "base": comparison.base,
                    "m": comparison.m,
                    "position": carry_transition.position,
                    "cycle_index": cycle_index,
                    "coefficient": carry_transition.coefficient,
                    "coefficient_fits_block": coefficient_fits_block,
                    "carry_in": carry_transition.carry_in,
                    "carry_out": carry_transition.carry_out,
                    "carry_block_value": carry_transition.block_value,
                    "carried_block": carried_block,
                    "remainder_in": remainder_transition.remainder_in,
                    "remainder_out": remainder_transition.remainder_out,
                    "long_division_block": actual_block,
                    "output_matches": carried_block == actual_block,
                    "visibility_event": _trace_visibility_event(
                        carry_transition.coefficient,
                        comparison.B,
                        carry_transition.carry_in,
                    ),
                }
            )

        rows.append(
            {
                "group": "state_map_summary",
                "n": comparison.n,
                "base": comparison.base,
                "m": comparison.m,
                "remainder_to_carry_functional": comparison.remainder_to_carry_map.is_functional,
                "remainder_to_carry_injective": comparison.remainder_to_carry_map.is_injective,
                "remainder_to_carry_fiber_signature": comparison.remainder_to_carry_map.fiber_signature,
                "remainder_to_carry_preimage_signature": comparison.remainder_to_carry_map.preimage_signature,
                "carry_to_remainder_functional": comparison.carry_to_remainder_map.is_functional,
                "carry_to_remainder_injective": comparison.carry_to_remainder_map.is_injective,
                "carry_to_remainder_fiber_signature": comparison.carry_to_remainder_map.fiber_signature,
                "carry_to_remainder_preimage_signature": comparison.carry_to_remainder_map.preimage_signature,
            }
        )
    return rows
