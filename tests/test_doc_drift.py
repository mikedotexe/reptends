import re
from pathlib import Path

from bridge_reptends import (
    certificate_first_scaffold_mapping_lint_payload,
    certificate_fixture_mapping_lint_payload,
    certificate_lean_fixture_payload,
    certificate_lean_stub_payload,
    load_claim_registry,
    load_lean_claim_carriers,
    load_lean_module_index,
    load_lean_open_claim_boundaries,
    load_lean_worked_examples,
    render_claim_table_lines,
    render_examples_open_boundary_note_lines,
    render_lean_claim_carrier_lines,
    render_lean_open_claim_boundary_lines,
    render_lean_module_index_lines,
    render_lean_worked_example_lines,
    render_geometric_stack_import_lines,
    render_open_claim_lines,
    render_open_claim_lean_support_lines,
    render_proof_status_footer_lines,
    render_proof_status_track_five_notes_lines,
    render_proof_system_legend_lines,
    render_qr_tour_import_lines,
    render_readme_lean_claim_surface_lines,
    render_registry_summary_lines,
    render_same_core_boundary_note_lines,
    render_theorem_guide_throughline_layer_lines,
    render_theorem_guide_module_index_source_lines,
    render_theorem_guide_next_frontier_lines,
    render_theorem_guide_status_source_lines,
    render_theorem_witness_summary_lines,
    render_theorem_witness_table_lines,
    render_throughline_research_thesis_lines,
    render_throughline_witness_ladder_lines,
    theorem_witnesses_by_claim,
    render_vocabulary_table_lines,
)
from bridge_reptends.registry import (
    render_carried_prefix_visibility_status_anchor_lines,
    render_carry_transducer_status_anchor_lines,
)


ROOT = Path(__file__).resolve().parent.parent

README = ROOT / "README.md"
AGENTS = ROOT / "AGENTS.md"
CLAUDE = ROOT / "CLAUDE.md"
DISCOVERIES = ROOT / "DISCOVERIES.md"
DOCS_DIR = ROOT / "docs"
HARDENING_ROADMAP = DOCS_DIR / "ROADMAP.md"
LEAN_GUIDE = ROOT / "lean" / "THEOREM_GUIDE.md"
QRT_SURFACE = ROOT / "lean" / "QRTour.lean"
GEOMETRIC_STACK_SURFACE = ROOT / "lean" / "GeometricStack.lean"
EXAMPLES_SURFACE = ROOT / "lean" / "QRTour" / "Examples.lean"
WITNESS_ATLAS = DOCS_DIR / "THEOREM_WITNESS_ATLAS.md"
AGDA_CORRESPONDENCE = DOCS_DIR / "AGDA_CORRESPONDENCE.md"
CARRY_TRANSDUCER = DOCS_DIR / "CARRY_TRANSDUCER.md"
CARRIED_PREFIX_VISIBILITY = DOCS_DIR / "CARRIED_PREFIX_VISIBILITY.md"
ORBIT_INSTRUMENT_VISIBILITY = DOCS_DIR / "ORBIT_INSTRUMENT_VISIBILITY.md"
OUTSIDE_READER_DOORWAY = DOCS_DIR / "OUTSIDE_READER_DOORWAY.md"
VISIBILITY_OPTICS_WORKBENCH = DOCS_DIR / "VISIBILITY_OPTICS_WORKBENCH.md"
INSTRUMENT_ATLAS = DOCS_DIR / "INSTRUMENT_ATLAS.md"
VISIBILITY_GEOMETRY = DOCS_DIR / "VISIBILITY_GEOMETRY.md"
CHART_INVARIANCE = DOCS_DIR / "CHART_INVARIANCE.md"
OBSERVABILITY_BOUNDARY = DOCS_DIR / "OBSERVABILITY_BOUNDARY.md"
OBSERVABILITY_PROBLEMS = DOCS_DIR / "OBSERVABILITY_PROBLEMS.md"
RESEARCH_BRIEF = DOCS_DIR / "RESEARCH_BRIEF.md"
SITE_DOCUMENT = ROOT / "site" / "src" / "components" / "FiniteReptendDocument.tsx"
SITE_ORBIT_GALLERY = ROOT / "site" / "src" / "components" / "OrbitInstrumentVisibilityGallery.tsx"
PUBLIC_DOCS = [README, AGENTS, CLAUDE, DISCOVERIES, *sorted(DOCS_DIR.glob("*.md"))]

BANNED_LEGACY_STRINGS = [
    "1/N = (1/B) × 1/(1 - k/B) = Σ k^j / B^(j+1)",
    "1/N = Σ k^j / B^(j+1)",
    "3 is an NQR, so 3/97 lives in the **NQR coset**.",
    "All EVEN [2,4,6,...]",
    "All CONSECUTIVE [1,2,3,...]",
    "### Agda (Formal Proofs)",
    "Agda formal proofs (uses postulates)",
]

AGDA_POSTULATE_NAMES = [
    "prime-97",
    "k97-is-qr-generator",
    "ord",
    "ord-spec",
    "ord-period",
    "orbitRem-periodic",
    "digitAt-periodic",
    "IsPrime",
    "order-spec",
    "order-divides-p-1",
    "fermat",
    "inverse",
    "inverse-spec",
    "inverse-nonzero",
    "euler-qr",
    "euler-nqr",
    "euler-qr-inverse",
    "ab-pos",
    "qr-count",
    "nqr-count",
    "nqr-as-translate",
    "qr-orbit-exhaustive",
]


def test_high_visibility_docs_do_not_reintroduce_legacy_claims() -> None:
    for path in PUBLIC_DOCS:
        text = path.read_text()
        for banned in BANNED_LEGACY_STRINGS:
            assert banned not in text, f"{path.name} reintroduced banned legacy text: {banned}"


def test_collaborator_wrappers_reference_exact_identity_and_canonical_docs() -> None:
    for path in [AGENTS, CLAUDE]:
        text = path.read_text()
        assert ("q/(B-k)" in text) or ("B = qN + k" in text)
        assert "docs/AGDA_CORRESPONDENCE.md" in text
        assert "docs/PROOF_STATUS_ATLAS.md" in text
        assert "docs/VOCABULARY.md" in text
        assert "proof-status atlas" in text
        assert "standard-label-first" in text
        assert "pedagogical companion surface" in text


def test_agda_surface_is_framed_honestly_in_public_docs() -> None:
    readme = README.read_text()
    correspondence = AGDA_CORRESPONDENCE.read_text()

    assert "docs/AGDA_CORRESPONDENCE.md" in readme
    assert "docs/CARRIED_PREFIX_VISIBILITY.md" in readme
    assert "pedagogical companion surface" in readme.lower()
    assert "theorem-complete formal backend" in readme.lower() or "theorem-complete backend" in readme.lower()

    assert correspondence.startswith("# Agda Proof-Surface Audit and Correspondence")
    assert "Future public prose must not imply Agda has full proof parity with Lean." in correspondence
    assert "locally provable in Agda" in correspondence
    assert "intentionally postulated but Lean-backed" in correspondence
    assert "open or out of scope" in correspondence
    assert "`0` locally provable in Agda" in correspondence
    assert "`16` intentionally postulated but Lean-backed" in correspondence
    assert "`6` open or out of scope" in correspondence
    assert "`b > 0`" in correspondence
    assert "`M > 1`" in correspondence

    for name in AGDA_POSTULATE_NAMES:
        assert f"`{name}`" in correspondence, f"missing Agda postulate from correspondence doc: {name}"


def test_agda_examples_annotate_local_vs_lean_backed_assumptions() -> None:
    prime97 = (ROOT / "agda" / "Examples" / "Prime97.agda").read_text()
    composite96 = (ROOT / "agda" / "Examples" / "Composite96.agda").read_text()

    assert "Local Agda proofs in this file" in prime97
    assert "Lean-backed postulates still assumed here" in prime97
    assert "This example is fully local to GeometricStack." in composite96


def test_discoveries_file_is_explicitly_reframed() -> None:
    text = DISCOVERIES.read_text()
    intro = "\n".join(text.splitlines()[:12])
    assert text.startswith("# Empirical Notes and Exact Consequences")
    assert "not the proof-status source of truth" in intro
    assert "empirical" in intro.lower()
    assert "exact consequences" in text.lower()


def test_theorem_surfaces_do_not_hardcode_codex_worktree_roots() -> None:
    for path in [README, DOCS_DIR / "PROOF_STATUS_ATLAS.md", LEAN_GUIDE, WITNESS_ATLAS]:
        assert "/Users/mikepurvis/.codex/worktrees/" not in path.read_text()


def test_carry_transducer_doc_records_exact_flagship_candidates() -> None:
    text = CARRY_TRANSDUCER.read_text()

    assert "## Flagship Candidate Statements" in text
    assert "preimage-fiber profile (state-merging atlas)" in text
    assert "`Positive candidate (restricted remainder-to-carry factorization)`" in text
    assert "`Obstruction candidate (core/output insufficiency)`" in text
    assert "`remainderToCarryFunctional`" in text
    assert "remainder-to-carry transition compatibility" in text
    assert "same-core family" in text
    assert "`249`" in text and "`498`" in text and "`996`" in text
    assert "`17 -> 34` selector-family shift" in text


def test_orbit_instrument_visibility_lens_stays_prominent_and_status_honest() -> None:
    readme = README.read_text()
    note = ORBIT_INSTRUMENT_VISIBILITY.read_text()
    carry_doc = CARRY_TRANSDUCER.read_text()
    theorem_guide = LEAN_GUIDE.read_text()
    observability_doc = OBSERVABILITY_BOUNDARY.read_text()
    roadmap = HARDENING_ROADMAP.read_text()
    site_document = SITE_DOCUMENT.read_text()
    gallery = SITE_ORBIT_GALLERY.read_text()

    assert "## Orbit, Instrument, Visibility" in readme
    assert "The reptend is the observed trace; the remainder orbit is the source; the" in readme
    assert "docs/ORBIT_INSTRUMENT_VISIBILITY.md" in readme
    assert "search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996" in readme
    assert "Visibility Optics workbench" in readme
    assert "search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20" in readme
    assert "search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20" in readme
    assert "Instrument Atlas" in readme
    assert "docs/INSTRUMENT_ATLAS.md" in readme
    assert "search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in readme
    assert "docs/VISIBILITY_GEOMETRY.md" in readme
    assert "docs/CHART_INVARIANCE.md" in readme
    assert "search-reptends chart-invariance --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in readme
    assert "docs/OUTSIDE_READER_DOORWAY.md" in readme
    assert "docs/VISIBILITY_OPTICS_WORKBENCH.md" in readme

    assert OUTSIDE_READER_DOORWAY.exists()
    doorway = OUTSIDE_READER_DOORWAY.read_text()
    assert doorway.startswith("# Outside Reader Doorway")
    assert "The decimal is a readout, not the object." in doorway
    assert "`1/97`" in doorway
    assert "`B = 100`" in doorway
    assert "`qk^j`" in doorway
    assert "remainder orbit" in doorway
    assert "finite carry window" in doorway
    assert "small_k_visibility_threshold" in doorway
    assert "carry_dfa_factorization" in doorway
    assert "search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20" in doorway
    assert "search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in doorway
    assert "INSTRUMENT_ATLAS.md" in doorway
    assert "VISIBILITY_GEOMETRY.md" in doorway
    assert "CHART_INVARIANCE.md" in doorway
    assert "not the proof-status source of truth" in doorway

    assert ORBIT_INSTRUMENT_VISIBILITY.exists()
    assert note.startswith("# Orbit, Instrument, Visibility")
    assert "reader-facing research lens, not a new theorem claim" in note
    assert "`carry_dfa_factorization` claim remains `open`" in note
    assert "minimal/global" in note
    assert "`small_k_visibility_threshold` also remains `open`" in note
    assert "Source: the remainder orbit" in note
    assert "Signal: the raw coefficient stream `qk^j`" in note
    assert "Instrument: the finite carry window" in note
    assert "Observation: the displayed reptend blocks" in note
    assert "Visibility Optics workbench" in note
    assert "search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20" in note
    assert "search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20" in note
    assert "search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in note
    assert "INSTRUMENT_ATLAS.md" in note
    assert "VISIBILITY_GEOMETRY.md" in note
    assert "CHART_INVARIANCE.md" in note
    assert "phase space" in note
    assert "capacity thresholds" in note
    assert "VISIBILITY_OPTICS_WORKBENCH.md" in note

    assert VISIBILITY_OPTICS_WORKBENCH.exists()
    workbench = VISIBILITY_OPTICS_WORKBENCH.read_text()
    assert workbench.startswith("# Visibility Optics Workbench")
    assert "Status: experimental finite-window workbench" in workbench
    assert "`small_k_visibility_threshold` and `carry_dfa_factorization` remain `open`" in workbench
    assert "`workbench_summary`" in workbench
    assert "`canonical_anchor`" in workbench
    assert "`ranked_case`" in workbench
    assert "`same_core_signal`" in workbench
    assert "`transparent_window`" in workbench
    assert "`early_carry_intrusion`" in workbench
    assert "`visible_state_compression`" in workbench
    assert "`hidden_graph_obstruction`" in workbench
    assert "`same_core_drift`" in workbench
    assert "Base-Instrument Comparison" in workbench
    assert "Base `30`" in workbench
    assert "search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20" in workbench
    assert "Instrument Atlas" in workbench
    assert "working_axiom_signal" in workbench
    assert "search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in workbench

    assert INSTRUMENT_ATLAS.exists()
    atlas = INSTRUMENT_ATLAS.read_text()
    assert atlas.startswith("# Instrument Atlas")
    assert "empirical finite-window research surface, not a theorem source" in atlas
    assert "reveal" in atlas and "absorb" in atlas and "distort" in atlas and "obstruct" in atlas
    assert "`small_k_visibility_threshold` and" in atlas
    assert "`carry_dfa_factorization` are still `open`" in atlas
    assert "search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in atlas
    assert "10:visible_state_compression -> 12:early_carry_intrusion -> 30:hidden_graph_obstruction" in atlas
    assert "recoverability_is_instrument_relative" in atlas
    assert "visible_trace_can_hide_state_obstruction" in atlas
    assert "VISIBILITY_GEOMETRY.md" in atlas
    assert "CHART_INVARIANCE.md" in atlas
    assert "search-reptends chart-invariance --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in atlas

    assert VISIBILITY_GEOMETRY.exists()
    geometry = VISIBILITY_GEOMETRY.read_text()
    assert geometry.startswith("# Visibility Geometry")
    assert "conceptual research lens, not a theorem source" in geometry
    assert "GeometricStack" in geometry
    assert "phase space" in geometry
    assert "capacity geometry" in geometry
    assert "Fiber Geometry" in geometry
    assert "Chart Geometry" in geometry
    assert "`small_k_visibility_threshold`" in geometry
    assert "`carry_dfa_factorization`" in geometry
    assert "10:visible_state_compression -> 12:early_carry_intrusion -> 30:hidden_graph_obstruction" in geometry
    assert "CHART_INVARIANCE.md" in geometry
    assert "search-reptends chart-invariance --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in geometry
    assert "QRTour/ChartInvariance.lean" in geometry
    assert "finite `ChartObservation` rows" in geometry
    assert "`ChartPairWitness` classifications" in geometry
    assert "`transparentWindow` and" in geometry
    assert "`hiddenGraphObstruction` as annotated state-map" in geometry

    assert CHART_INVARIANCE.exists()
    chart_doc = CHART_INVARIANCE.read_text()
    assert chart_doc.startswith("# Chart Invariance")
    assert "empirical finite-window chart comparison, not a theorem source" in chart_doc
    assert "QRTour/ChartInvariance.lean" in chart_doc
    assert "VisibilitySignalClass" in chart_doc
    assert "ChartObservation" in chart_doc
    assert "ChartObservation.derivedSignalClass?" in chart_doc
    assert "ChartSignature.ofDenominator" in chart_doc
    assert "compactObservations" in chart_doc
    assert "transparentWindow" in chart_doc
    assert "earlyCarryIntrusion" in chart_doc
    assert "visibleStateCompression" in chart_doc
    assert "hiddenGraphObstruction" in chart_doc
    assert "partial classifier returns `none`" in chart_doc
    assert "compactObservations_derivedSignalAgreement_count = 10" in chart_doc
    assert "B`, `q`, `k`, raw-prefix, and carry-position data" in chart_doc
    assert "a decimal or block expansion is a readout" in chart_doc
    assert "raw finite evidence from the smaller signature" in chart_doc
    assert "ChartPairWitness" in chart_doc
    assert "ChartInvarianceExamples" in chart_doc
    assert "compactBasePairWitnesses" in chart_doc
    assert "countWitnessesForBasePair" in chart_doc
    assert "countInvariantWitnessesForBasePair" in chart_doc
    assert "10/12` has `2` invariant and `2` distortion witnesses" in chart_doc
    assert "CleanChartDistortion" in chart_doc
    assert "claim-free in the Lean module index" in chart_doc
    assert "clean chart distortion" in chart_doc
    assert "absorption-stable signal" in chart_doc
    assert "chart_pair_summary" in chart_doc
    assert "chart_distortion_witness" in chart_doc
    assert "`small_k_visibility_threshold`" in chart_doc
    assert "`carry_dfa_factorization`" in chart_doc
    assert "10:visible_state_compression -> 12:early_carry_intrusion -> 30:hidden_graph_obstruction" in chart_doc

    assert "observed trace; the remainder orbit is" in carry_doc
    assert "finite carry window is the instrument" in carry_doc
    assert "carry-propagated block normalization" in carry_doc
    assert "visibility_optics_workbench_rows" in carry_doc
    assert "Visibility Optics workbench" in carry_doc
    assert "VISIBILITY_OPTICS_WORKBENCH.md" in carry_doc
    assert "base `30` as data" in carry_doc
    assert "search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20" in carry_doc
    assert "search-reptends visibility-coefficient-conflicts --max 1200 --base 10 --blocks 8 --top 20" in carry_doc
    assert "search-reptends visibility-coefficient-conflict-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in carry_doc
    assert "search-reptends visibility-coefficient-conflict-families --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in carry_doc
    assert "search-reptends visibility-composite68-base-sweep --max-base 120 --blocks 8 --top 20" in carry_doc
    assert "search-reptends visibility-composite68-congruence-family --max-base 120 --max-m 8 --blocks 8 --top 0" in carry_doc
    assert "Certificate Workbench" in carry_doc
    assert "search-reptends visibility-certificate-workbench --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in carry_doc
    assert "empirical/open-boundary tooling only" in carry_doc
    assert "does not promote\n`small_k_visibility_threshold`, `carry_dfa_factorization`" in carry_doc
    for doc in [carry_doc, theorem_guide, observability_doc]:
        assert "search-reptends observability-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50" in doc
        assert "search-reptends observability-program-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50" in doc
        assert "search-reptends observability-target-split --max 1200 --bases 7,10,12,30 --blocks 8 --top 50" in doc
        assert "search-reptends observability-target-signatures --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in doc
        assert "search-reptends observability-mod-stable-carry-loss --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in doc
        assert "search-reptends observability-shape13-k4-mod-stable-carry-loss --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in doc
        assert "search-reptends observability-instrument-compare --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in doc
        assert "search-reptends observability-shape17-k4-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in doc
        assert "search-reptends observability-next-source-shape-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in doc
        assert "search-reptends observability-shape187-k188-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in doc
        assert "coefficient information loss" in doc
        assert "positive reconstruction" in doc
        assert "factor-through target" in doc
        assert "observability_positive_reconstruction_candidate" in doc
        assert "positive_reconstruction_source_pinned" in doc
        assert "positive_reconstruction_source_status" in doc
        assert "positive_reconstruction_lean_support_status" in doc
        assert "positive_reconstruction_functional_theorem" in doc
        assert "positive_reconstruction_factor_through_theorem" in doc
        assert "finite_remainder_state_injective_on_window" in doc
        assert "remainder_state_window" in doc
        assert "raw_coefficient_window" in doc
        assert "remainder_state_window_injective" in doc
        assert "positive_reconstruction_arithmetic_criterion_id" in doc
        assert "positive_reconstruction_hyp_remainder_state_window_injective" in doc
        assert "finite_remainder_power_residue_no_collision" in doc
        assert "remainder_power_residue_window" in doc
        assert "positive_reconstruction_hyp_remainder_power_residue_window_injective" in doc
        assert "finite_remainder_power_residue_no_wrap" in doc
        assert "remainder_power_unreduced_window" in doc
        assert "positive_reconstruction_hyp_remainder_power_residue_no_wrap" in doc
        assert "BlockCoordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup" in doc
        assert "BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup" in doc
        assert "BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup" in doc
        assert "BlockCoordinate.remainderK_powerResidues_nodup_of_remainderK_pow_lt_modulus" in doc
        assert "BlockCoordinate.stateAlignments_remainderIn_nodup_of_remainderK_pow_lt_modulus" in doc
        assert "BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_pow_lt_modulus" in doc
        assert "BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_pow_lt_modulus" in doc
        assert "List.functionalOnFst_of_map_fst_nodup" in doc
        assert "BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup" in doc
        assert "BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup" in doc
        assert "QRTour.Prime97.coordinate_stateAlignments_remainderIn_nodup_eight_two" in doc
        assert "QRTour.Composite996.actual996_stateAlignments_remainderIn_nodup_eight_one" in doc
        assert "QRTour.FutureBase10N98.coordinate_stateAlignments_remainderIn_nodup_eight_one" in doc
        assert "QRTour.FutureBase12N142.coordinate_stateAlignments_remainderIn_nodup_eight_one" in doc
        assert "QRTour.FutureBase7N47.coordinate_stateAlignments_remainderIn_nodup_eight_one" in doc
        assert "QRTour.FutureBase12N71.coordinate_stateAlignments_remainderIn_nodup_eight_one" in doc
        assert "QRTour.FutureBase10N49.coordinate_stateAlignments_remainderIn_nodup_eight_one" in doc
        assert "QRTour.FutureBase30N299.coordinate_stateAlignments_remainderIn_nodup_eight_one" in doc
        assert "QRTour.FutureBase7N170.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert "first_unpinned_positive_reconstruction_tuple" in doc
        assert "first_unpinned_positive_reconstruction_remainder_power_residue_window" in doc
        assert "first_unpinned_positive_reconstruction_family_seed_tuples" in doc
        assert "[7, 340, 3, 343, 1, 3, 1, 299]" in doc
        assert "[1, 3, 9, 27, 81, 243, 49, 147]" in doc
        assert (
            "QRTour.Base7K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "use_lean_proved_family_criterion_before_source_pinning_more_examples"
            in doc
        )
        assert "first_uncovered_positive_reconstruction_tuple" in doc
        assert "first_uncovered_positive_reconstruction_remainder_power_residue_window" in doc
        assert "QRTour.FutureBase10N997.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert (
            "QRTour.Base30K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base30K3PositiveReconstruction.n299_n897_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[10, 498, 3, 1000, 2, 4, 1, 928]" in doc
        assert (
            "QRTour.Base10K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10K4PositiveReconstruction.n498_n996_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[83, 166, 249, 332, 498, 996]" in doc
        assert "[12, 575, 3, 1728, 3, 3, 1, 1053]" in doc
        assert "[1, 3, 9, 27, 81, 243, 154, 462]" in doc
        assert "QRTour.FutureBase12N575.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[12, 75, 3, 1728, 23, 3, 1, 1161]" in doc
        assert "[1, 3, 9, 27, 6, 18, 54, 12]" in doc
        assert (
            "QRTour.Base12K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12K3PositiveReconstruction.n75_n575_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[23, 25, 69, 75, 115, 345, 575, 1725]" in doc
        assert "[7, 1199, 4, 2401, 2, 3, 1, 1284]" in doc
        assert "[1, 3, 9, 27, 81, 243, 729, 988]" in doc
        assert "QRTour.FutureBase7N1199.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[10, 294, 4, 10000, 34, 4, 1, 1776]" in doc
        assert "[1, 4, 16, 64, 256, 142, 274, 214]" in doc
        assert "QRTour.FutureBase10N294.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[7, 109, 4, 2401, 22, 3, 1, 2119]" in doc
        assert "[1, 3, 9, 27, 81, 25, 75, 7]" in doc
        assert (
            "QRTour.Base7Stride4K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7Stride4K3PositiveReconstruction.n109_n1199_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[109, 218, 1199, 2398]" in doc
        assert "[1, 2, 11, 22]" in doc
        assert "[7, 46, 2, 49, 1, 3, 2, 2171]" in doc
        assert "[1, 3, 9, 27, 35, 13, 39, 25]" in doc
        assert "QRTour.FutureBase7N46.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
            in doc
        )
        assert (
            "QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
            in doc
        )
        assert "[7, 141, 4, 2401, 17, 4, 1, 2353]" in doc
        assert "[1, 4, 16, 64, 115, 37, 7, 28]" in doc
        assert "QRTour.FutureBase7N141.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[10, 714, 4, 10000, 14, 4, 1, 2496]" in doc
        assert "[1, 4, 16, 64, 256, 310, 526, 676]" in doc
        assert (
            "QRTour.Base10Stride4K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10Stride4K4PositiveReconstruction.n294_n714_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[49, 98, 119, 147, 196, 238, 294, 357, 476, 588, 714, 833]" in doc
        assert "[12, 146, 4, 20736, 142, 4, 1, 4352]" in doc
        assert "[1, 4, 16, 64, 110, 2, 8, 32]" in doc
        assert "QRTour.FutureBase12N146.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[10, 769, 4, 10000, 13, 3, 1, 4707]" in doc
        assert "[1, 3, 9, 27, 81, 243, 729, 649]" in doc
        assert "QRTour.FutureBase10N769.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[7, 345, 6, 117649, 341, 4, 1, 5534]" in doc
        assert "[1, 4, 16, 64, 256, 334, 301, 169]" in doc
        assert "QRTour.FutureBase7N345.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[7, 465, 6, 117649, 253, 4, 1, 7901]" in doc
        assert "[1, 4, 16, 64, 256, 94, 376, 109]" in doc
        assert (
            "QRTour.Base7Stride6K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7Stride6K4PositiveReconstruction.n345_n465_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[7, 542, 5, 16807, 31, 5, 1, 8472]" in doc
        assert "[1, 5, 25, 125, 83, 415, 449, 77]" in doc
        assert "QRTour.FutureBase7N542.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[12, 73, 4, 20736, 284, 4, 1, 8704]" in doc
        assert "[1, 4, 16, 64, 37, 2, 8, 32]" in doc
        assert (
            "QRTour.Base12Stride4K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12Stride4K4PositiveReconstruction.n73_n146_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[71, 73, 142, 146, 284, 292, 5183, 10366, 20732]" in doc
        assert "[12, 47, 2, 144, 3, 3, 2, 9639]" in doc
        assert "[1, 3, 9, 27, 34, 8, 24, 25]" in doc
        assert "QRTour.FutureBase12N47.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
            in doc
        )
        assert (
            "QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
            in doc
        )
        assert "[12, 141, 2, 144, 1, 3, 2, 10125]" in doc
        assert "[1, 3, 9, 27, 81, 102, 24, 72]" in doc
        assert (
            "QRTour.Base12Stride2K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12Stride2K3PositiveReconstruction.n47_n141_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[47, 141]" in doc
        assert "[1, 3]" in doc
        assert "[30, 794, 3, 27000, 34, 4, 1, 12776]" in doc
        assert "[1, 4, 16, 64, 256, 230, 126, 504]" in doc
        assert "QRTour.FutureBase30N794.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[7, 113, 3, 343, 3, 4, 2, 13444]" in doc
        assert "[1, 4, 16, 64, 30, 7, 28, 112]" in doc
        assert "QRTour.FutureBase7N113.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
            in doc
        )
        assert (
            "QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
            in doc
        )
        assert "[12, 691, 4, 20736, 30, 6, 1, 20736]" in doc
        assert "[1, 6, 36, 216, 605, 175, 359, 81]" in doc
        assert "QRTour.FutureBase12N691.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[30, 397, 3, 27000, 68, 4, 1, 25552]" in doc
        assert "[1, 4, 16, 64, 256, 230, 126, 107]" in doc
        assert (
            "QRTour.Base30Stride3K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base30Stride3K4PositiveReconstruction.n397_n794_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[397, 794, 1588, 6749, 13498, 26996]" in doc
        assert "[1, 2, 4, 17, 34, 68]" in doc
        assert "[10, 578, 5, 100000, 173, 6, 1, 26432]" in doc
        assert "[1, 6, 36, 216, 140, 262, 416, 184]" in doc
        assert "QRTour.FutureBase10N578.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[10, 277, 5, 100000, 361, 3, 1, 31479]" in doc
        assert "[1, 3, 9, 27, 81, 243, 175, 248]" in doc
        assert "QRTour.FutureBase10N277.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[7, 669, 7, 823543, 1231, 4, 1, 32398]" in doc
        assert "[1, 4, 16, 64, 256, 355, 82, 328]" in doc
        assert "QRTour.FutureBase7N669.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[7, 71, 6, 117649, 1657, 2, 1, 46404]" in doc
        assert "[1, 2, 4, 8, 16, 32, 64, 57]" in doc
        assert "QRTour.FutureBase7N71.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[7, 118, 6, 117649, 997, 3, 1, 47027]" in doc
        assert "[1, 3, 9, 27, 81, 7, 21, 63]" in doc
        assert "QRTour.FutureBase7N118.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[7, 997, 6, 117649, 118, 3, 1, 49345]" in doc
        assert "[1, 3, 9, 27, 81, 243, 729, 193]" in doc
        assert (
            "QRTour.Base7Stride6K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base7Stride6K3PositiveReconstruction.n118_n997_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[59, 118, 997, 1994, 58823, 117646]" in doc
        assert "[1, 2]" in doc
        assert "[10, 289, 5, 100000, 346, 6, 1, 52864]" in doc
        assert "[1, 6, 36, 216, 140, 262, 127, 184]" in doc
        assert "[10, 578, 5, 100000, 173, 6, 1, 26432]" in doc
        assert (
            "QRTour.Base10Stride5K6PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10Stride5K6PositiveReconstruction.n289_n578_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[17, 34, 173, 289, 346, 578, 2941, 5882, 49997, 99994]" in doc
        assert "[12, 226, 5, 248832, 1101, 6, 1, 62208]" in doc
        assert "[1, 6, 36, 216, 166, 92, 100, 148]" in doc
        assert "QRTour.FutureBase12N226.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase12N226.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
            in doc
        )
        assert (
            "QRTour.FutureBase12N226.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
            in doc
        )
        assert "[7, 338, 3, 343, 1, 5, 2, 64744]" in doc
        assert "[1, 5, 25, 125, 287, 83, 77, 47]" in doc
        assert "QRTour.FutureBase7N338.coordinate_remainderK_powerResidues_nodup_eight" in doc
        assert (
            "QRTour.FutureBase7N338.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
            in doc
        )
        assert (
            "QRTour.FutureBase7N338.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
            in doc
        )
        assert "[12, 149, 5, 248832, 1670, 2, 1, 70144]" in doc
        assert "[1, 2, 4, 8, 16, 32, 64, 128]" in doc
        assert "QRTour.FutureBase12N149.coordinate_remainderK_pow_lt_modulus_eight" in doc
        assert "QRTour.FutureBase12N149.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert "[12, 289, 5, 248832, 861, 3, 1, 74115]" in doc
        assert "[1, 3, 9, 27, 81, 243, 151, 164]" in doc
        assert (
            "QRTour.Base12Stride5K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base12Stride5K3PositiveReconstruction.n289_n861_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[17, 41, 51, 119, 123, 287, 289, 357, 697, 861, 867, 2023, 2091, 4879, 6069, 11849, 14637, 35547, 82943, 248829]" in doc
        assert "[10, 641, 5, 100000, 156, 4, 1, 76384]" in doc
        assert "[1, 4, 16, 64, 256, 383, 250, 359]" in doc
        assert (
            "QRTour.Base10Stride5K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
            in doc
        )
        assert (
            "QRTour.Base10Stride5K4PositiveReconstruction.n641_n1282_powerResidues_nodup_eight_pair"
            in doc
        )
        assert "[641, 1282, 1923, 2564, 3846, 7692, 8333, 16666, 24999, 33332, 49998, 99996]" in doc
        assert "[10, 361, 5, 100000, 277, 3, 1, 82603]" in doc
        assert "[1, 3, 9, 27, 81, 243, 7, 21]" in doc
        assert "pursue_family_criterion_before_source_pinning_more_examples" in doc
        assert "prove_or_reject_same_base_block_remainder_power_no_collision_family" in doc
        assert "BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderToCoefficientFunctional" in doc
        assert "QRTour.Prime97.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two" in doc
        assert "QRTour.Composite996.actual996_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert "QRTour.FutureBase10N98.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert "QRTour.FutureBase12N142.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert "QRTour.FutureBase7N47.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert "QRTour.FutureBase12N71.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert "QRTour.FutureBase10N49.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert "QRTour.FutureBase30N299.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert "QRTour.FutureBase7N170.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in doc
        assert "raw_coefficient_nat" in doc
        assert "coefficient_mod_block_base" in doc
        assert "carried_block_value" in doc
        assert "carry_state" in doc
        assert "remainder_state" in doc
        assert "displayed_prefix" in doc
        assert "window-level certificate" in doc
        assert "empirical/open-boundary target-split tooling" in doc.replace("\n", " ")
        assert "observability_target_summary_signature" in doc
        assert "observability_target_signature_family" in doc
        assert "empirical/open-boundary target-signature tooling" in doc.replace("\n", " ")
        assert "observability_mod_stable_carry_loss_case" in doc
        assert "empirical/open-boundary mod-stable carry-loss tooling" in doc.replace("\n", " ")
        assert "(30, 26, 1, 30, 1, 4, 5, 11927264)" in doc
        assert "observability_shape13_k4_mod_stable_carry_loss_summary" in doc
        assert "observability_shape13_k4_mod_stable_carry_loss_member" in doc
        assert "periodic_modulus=13;k=4;position_gap=6" in doc
        assert "(30, 13, 1, 30, 2, 4, 5, 23854528)" in doc
        assert "QRTour.FutureBase30N13.coordinate_stateAlignments_zero_six_certifiedConflict_eight_five" in doc
        assert "QRTour.FutureBase30N26.coordinate_stateAlignments_one_seven_certifiedConflict_eight_five" in doc
        assert "QRTour.Shape13K4.base30_core13_to_double26_conflict_shift_scaled" in doc
        assert "QRTour.Shape13K4.base30_n26_sameCore_scale_two_hiddenCarryBlockValue_shift" in doc
        assert "sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two" in doc
        assert "SameCoreScaleTwoHiddenCarryBlockValueHypotheses" in doc
        assert (
            "sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two_of_exportedHypotheses"
            in doc
        )
        assert "QRTour.Shape13K4.base30_n26_scaleTwoHiddenCarryBlockValueHypotheses" in doc
        assert "basePrimeSupportFactor * 2 = k" in doc
        assert "shape13_k4_hyp_base_prime_support_times_two_eq_k" in doc
        assert "shape13_k4_hyp_scaled_quotient_remainders_lt_gap" in doc
        assert "shape13_k4_hyp_scaled_block_remainders_lt_block_base" in doc
        assert "shape13_k4_scale_two_hypotheses_hold" in doc
        assert "shape13_k4_scale_two_failure_reason" in doc
        assert "shape13_k4_scale_two_unnamed_candidate_members" in doc
        assert "shape13_k4_scale_two_unnamed_candidate_tuples" in doc
        assert "shape13_k4_scale_two_candidate_mining_status" in doc
        assert "no_unnamed_scale_two_ready_members_under_current_bounds" in doc
        assert "base_prime_support_times_two_ne_k" in doc
        assert "manual probe found no additional members" in doc.replace("\n", " ")
        assert "max_n=2000" in doc
        assert (
            "do_not_add_new_shape13_k4_finite_package_until_wider_scan_emits_new_member"
            in doc
        )
        assert "FactorsThrough" in doc
        assert "not_factorsThrough_of_collision" in doc
        assert "List.functionalOnFst_iff_factorsThrough_memberSubtype" in doc
        assert "BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_iff_factorsThrough_memberSubtype" in doc
        assert "BlockCoordinate.stateAlignments_not_remainderToCoefficientFactorsThrough_of_not_remainderToCoefficientFunctional" in doc
        assert "BlockCoordinate.StateAlignmentCertifiedConflict.not_remainderToCoefficientFactorsThrough" in doc
        assert "QRTour.Composite68.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one" in doc
        assert "QRTour.Composite68Base30.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one" in doc
        assert "factor-through obstruction" in doc
        assert "empirical/open-boundary program" in doc.replace("\n", " ")
        assert "empirical/open-boundary observability tooling" in doc.replace("\n", " ")
        assert "small_k_visibility_threshold" in doc
        assert "carry_dfa_factorization" in doc
    for doc in [carry_doc, theorem_guide, observability_doc]:
        normalized = doc.replace("\n", " ")
        assert "source symmetry shape" in normalized
        assert "hide, reveal, or shift" in normalized
        assert "empirical/open-boundary instrument comparison" in normalized
        assert "Shape13/K4 mod-stable carry-loss classifier" in normalized
        assert "empirical/open-boundary Shape13/K4" in normalized
        assert "finite Lean support" in normalized
        assert "N = 17" in normalized
        assert "N = 34" in normalized
        assert "N = 68" in normalized
        assert "empirical/open-boundary family classification" in normalized
        assert "finite Shape17/K4 shift witness" in normalized
        assert "periodic_modulus=187;k=188;position_gap=6" in normalized
        assert "finite_only_hidden_conflict" in normalized
        assert "same-position" in normalized
        assert "same_position_scaling_proved_by_arithmetic_criterion" in normalized
        assert "same_position_scaling_criterion_candidate" in normalized
        assert "BlockCoordinate.samePositionIdempotent_hiddenCarryBlockValue" in normalized
        assert "samePositionIdempotent_hiddenCarryBlockValue" in normalized
        assert "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses" in normalized
        assert (
            "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses.idempotent_remainder"
            in normalized
        )
        assert (
            "BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses"
            in normalized
        )
        assert (
            "QRTour.FutureBase30N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
            in normalized
        )
        assert (
            "QRTour.FutureBase10N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
            in normalized
        )
        assert (
            "QRTour.FutureBase12N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
            in normalized
        )
        assert (
            "QRTour.FutureBase30N748.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
            in normalized
        )
        assert "same_position_scaling_exported_hypothesis_record" in normalized
        assert "same_position_scaling_idempotent_remainder_projection" in normalized
        assert "same_position_scaling_exported_hypothesis_adapter" in normalized
        assert "same_position_scaling_intended_proof_path" in normalized
        assert "same_position_scaling_named_hypothesis_instantiation" in normalized
        assert "same_position_scaling_named_finite_conflict_instantiation" in normalized
        assert "QRTour.FutureBase10N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two" in normalized
        assert "QRTour.FutureBase12N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two" in normalized
        assert "QRTour.FutureBase10N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_two" in normalized
        assert "QRTour.FutureBase30N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two" in normalized
        assert "QRTour.FutureBase30N748.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two" in normalized
        assert "QRTour.Shape187K188.base30_default_samePositionIdempotent_hiddenCarryBlockValue_one_two_pair" in normalized
        assert "QRTour.FutureBase30N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_one" in normalized
        assert "QRTour.FutureBase30N748.coordinate_stateAlignments_one_two_certifiedConflict_eight_one" in normalized
        assert "QRTour.FutureBase10N17.coordinate_stateAlignments_zero_four_certifiedConflict_eight_two" in normalized
        assert "QRTour.FutureBase10N34.coordinate_stateAlignments_one_five_certifiedConflict_eight_two" in normalized
        assert "QRTour.Shape17K4.base10_core17_to_composite68_conflict_shift_exact" in normalized
        assert "QRTour.Shape17K4.base10_core17_to_double34_conflict_shift_scaled" in normalized
        assert "not a global same-core classification theorem" in normalized
        assert "sameCoreCompatible_rawCoefficient_shift_scaled_one" in normalized
        assert "sameCoreCompatible_incomingCarry_shift_scaled_one" in normalized
        assert "sameCoreCompatible_canonicalCarryBlockValue_shift_scaled_one" in normalized
        assert "sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one" in normalized
        assert "nat_mul_div_eq_mul_div_iff_mul_mod_lt" in normalized
        assert "nat_mul_mod_eq_mul_mod_iff_mul_mod_lt" in normalized
        assert "QRTour.Shape17K4.base10_n68_sameCore_scale_one_hiddenCarryBlockValue_shift" in normalized
        assert "QRTour.Shape17K4.base10_n34_sameCore_scale_two_hiddenCarryBlockValue_shift" in normalized
        assert "QRTour.Shape17K4.base30_n68_sameCore_scale_one_hiddenCarryBlockValue_shift" in normalized
        assert "QRTour.Shape17K4.base30_n34_sameCore_scale_two_hiddenCarryBlockValue_shift" in normalized
        assert "same_core_shift_proved_by_arithmetic_criterion" in normalized
        assert "same_core_shift_criterion_candidate" in normalized
        assert "finite_only_hidden_conflict" in normalized
        assert "least-lookahead" in normalized
    assert "factor-through" in observability_doc
    assert "observational indistinguishability" in observability_doc
    assert "External Source Map" in observability_doc
    assert "Frougny 1992" in observability_doc
    assert "Reutenauer-Schutzenberger 1991" in observability_doc
    assert "Blackwell-Koopmans 1957" in observability_doc
    assert "Cobham 1969" in observability_doc
    assert "Hermann-Krener 1977" in observability_doc
    assert "Geiger-Kubin 2017" in observability_doc
    assert "search-reptends visibility-certificate-lean-fixtures --max 1200 --bases 7,10,12,30 --blocks 8" in carry_doc
    assert "certificate-lean-fixtures-v1" in carry_doc
    assert "copyable_lean_stub" in carry_doc
    assert "search-reptends visibility-certificate-lean-stubs --max 1200 --bases 7,10,12,30 --blocks 8" in carry_doc
    assert "certificate-lean-stubs-v1" in carry_doc
    assert "certificate-fixture-mapping-lint-v1" in carry_doc
    assert "source_pinning_recipe" in carry_doc
    assert "repeatable path from lint output to Lean theorem names" in carry_doc
    assert "search-reptends visibility-certificate-lean-stubs --max 120 --bases 7,10,12,30 --blocks 8 --first-scaffold-only" in carry_doc
    assert "QRTour.FutureBase30N7" in carry_doc
    assert "QRTour.FutureBase30N14" in carry_doc
    assert "QRTour.FutureBase30N28" in carry_doc
    assert "QRTour.FutureBase12N10" in carry_doc
    assert "QRTour.FutureBase10N102" in carry_doc
    assert "QRTour.FutureBase7N5" in carry_doc
    assert "QRTour.FutureBase12N5" in carry_doc
    assert "QRTour.FutureBase30N34" in carry_doc
    assert "QRTour.FutureBase7N93" in carry_doc
    assert "QRTour.FutureBase10N39" in carry_doc
    assert "QRTour.FutureBase10N78" in carry_doc
    assert "QRTour.FutureBase10N96" in carry_doc
    assert "QRTour.FutureBase12N35" in carry_doc
    assert "QRTour.FutureBase12N31" in carry_doc
    assert "lean_package_plan" in carry_doc
    assert "coordinate_stateAlignments_zero_three_certifiedConflict_eight_two" in carry_doc
    assert "base30_n7_m1_blocks8_L2_not_remainderToCoefficientFunctional" in carry_doc
    assert "coordinate_stateAlignments_one_four_certifiedConflict_eight_two" in carry_doc
    assert "base30_n14_m1_blocks8_L2_not_remainderToCoefficientFunctional" in carry_doc
    assert "coordinate_stateAlignments_two_five_certifiedConflict_eight_two" in carry_doc
    assert "base30_n28_m1_blocks8_L2_not_remainderToCoefficientFunctional" in carry_doc
    assert "coordinate_stateAlignments_one_five_certifiedConflict_eight_three" in carry_doc
    assert "base12_n10_m1_blocks8_L3_not_remainderToCoefficientFunctional" in carry_doc
    assert "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one" in carry_doc
    assert "base10_n102_m4_blocks8_L1_not_remainderToCoefficientFunctional" in carry_doc
    assert "coordinate_stateAlignments_zero_four_certifiedConflict_eight_five" in carry_doc
    assert "base7_n5_m1_blocks8_L5_not_remainderToCoefficientFunctional" in carry_doc
    assert "coordinate_stateAlignments_zero_four_certifiedConflict_eight_four" in carry_doc
    assert "base12_n5_m1_blocks8_L4_not_remainderToCoefficientFunctional" in carry_doc
    assert "base30_n34_m3_blocks8_L1_not_remainderToCoefficientFunctional" in carry_doc
    assert "base7_n93_m6_blocks8_L1_not_remainderToCoefficientFunctional" in carry_doc
    assert "base10_n39_m5_blocks8_L1_not_remainderToCoefficientFunctional" in carry_doc
    assert "base10_n78_m5_blocks8_L1_not_remainderToCoefficientFunctional" in carry_doc
    assert "base10_n96_m2_blocks8_L3_not_remainderToCoefficientFunctional" in carry_doc
    assert "base12_n35_m2_blocks8_L3_not_remainderToCoefficientFunctional" in carry_doc
    assert "base12_n31_m6_blocks8_L1_not_remainderToCoefficientFunctional" in carry_doc
    assert "source-ready" in carry_doc
    assert "--namespace QRTour.FutureN7" in carry_doc
    assert "stub scaffold/lint export" in carry_doc
    assert "does not write Lean files or promote a claim" in carry_doc
    assert "empirical/open-boundary certificate-to-Lean tooling" in carry_doc
    assert "not a theorem\nsurface, registry promotion, theorem-witness record, or atlas claim" in carry_doc
    assert "(base, N, m, B, q, k, L, gap) = (10, 68, 4, 10000, 147, 4, 1, 6208)" in carry_doc
    assert "remainder state `4` appears at positions `1` and `5`" in carry_doc
    assert "periodic_modulus=17;k=4;remainder_state=4;positions=[1, 5];carry_states=[0, 60];output_hidden=true" in carry_doc
    assert "classify_composite68_cross_base_hidden_output_conflict" in carry_doc
    assert "`10, 30, 32, 64, 66, 72, 98, 100`" in carry_doc
    assert "`B mod 68 = 4`" in carry_doc
    assert "finite Lean response to that recommendation has now\nlanded" in carry_doc
    assert "remaining open boundary is arithmetic classification" in carry_doc.replace("\n", " ")
    assert "4^1 ≡ 4^5 (mod 68)" in carry_doc
    assert "B ≡ 4 (mod 68)" in carry_doc
    assert "empirical theorem-candidate selector rather than a registry claim" in carry_doc
    assert "QRTour.Composite68.coordinate_not_coefficientFunctional_eight_one" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_not_coefficientFunctional_eight_one" in carry_doc
    assert "(base, N, m, B, q, k, L, gap) = (30, 68, 3, 27000, 397, 4, 1, 10208)" in carry_doc
    assert "raw coefficients `1588` and `406528`" in carry_doc
    assert "hidden carried block value `1588`" in carry_doc
    assert "BlockCoordinate.not_coefficientFunctional_one_five_of_remainderK_eq_four" in carry_doc
    assert "BlockCoordinate.stateAlignments_remainderIn_one_eq_five_of_modulus_eq_sixty_eight" in carry_doc
    assert "BlockCoordinate.not_coefficientFunctional_one_five_of_modulus_eq_sixty_eight" in carry_doc
    assert "BlockCoordinate.remainderK_eq_four_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.not_coefficientFunctional_one_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.incomingCarry_one_eq_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.incomingCarry_five_eq_sixty_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.incomingCarry_hiddenOutput_one_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "QRTour.Composite68.coordinate_incomingCarry_hiddenOutput_one_five" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_incomingCarry_hiddenOutput_one_five" in carry_doc
    assert "BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "composite68_suffixCarry_five_eq_sixty_of_tailCarry_le_nine_hundred_sixty_three" in carry_doc
    assert "composite68_suffixCarry_one_eq_zero_of_tailCarry_le_nine_hundred_sixty_three" in carry_doc
    assert "BlockCoordinate.incomingCarry_step_recurrence" in carry_doc
    assert "BlockCoordinate.traceRawWord_carryIn_le_incomingCarry" in carry_doc
    assert "BlockCoordinate.visibleCarryTrace_carryIn_le_incomingCarry" in carry_doc
    assert "BlockCoordinate.stateAlignments_carryIn_le_incomingCarry" in carry_doc
    assert "BlockCoordinate.incomingCarry_seven_eq_nine_hundred_sixty_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_any_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_of_carry_states_zero_sixty" in carry_doc
    assert "QRTour.Composite68.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry" in carry_doc
    assert "QRTour.Composite68.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero" in carry_doc
    assert "certified finite-trace bridge" in carry_doc
    assert "fixed-window theorem" in carry_doc
    assert "the `8/1` finite trace itself supplies the `(0, 60)` carry certificate" in carry_doc.replace("\n", " ")
    assert "same finite carry states are already forced on the `8/0` trace" in carry_doc.replace("\n", " ")
    assert "positive lookahead is still used for the certified output-agreement obstruction window" in carry_doc.replace("\n", " ")
    assert "finite carry entering the `4^7` block is at most `963`" in carry_doc.replace("\n", " ")
    assert "The universal suffix bound is now Lean-proved for the `N = 68`, `B ≡ 4 (mod 68)` family" in carry_doc.replace("\n", " ")
    assert "all-lookahead eight-block carry-state theorem" in carry_doc.replace("\n", " ")
    assert "obstruction-first finite visibility theorem" in carry_doc
    assert "BlockCoordinate.stateAlignments_one_five_hiddenCoefficientConflict_eight_any_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.stateAlignments_one_five_certifiedVisibilityObstruction_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "QRTour.Composite68.coordinate_stateAlignments_one_five_hiddenCoefficientConflict_eight_one" in carry_doc
    assert "QRTour.Composite68.coordinate_stateAlignments_one_five_certifiedVisibilityObstruction_eight_one" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_one_five_hiddenCoefficientConflict_eight_one" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_one_five_certifiedVisibilityObstruction_eight_one" in carry_doc
    assert "lookaheadCertificateHolds 8 L" in carry_doc
    assert "beyond the stated certificate" in carry_doc
    assert "BlockCoordinate.truncatedVisiblePrefixRemainder_one_eq_rawCoefficient_mod_blockBase" in carry_doc
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_seventy_five" in carry_doc
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_seventy_four" in carry_doc
    assert "BlockCoordinate.truncatedVisiblePrefixRemainder_two_eq_rawCoefficient_suffix_mod_blockBase_sq" in carry_doc
    assert "BlockCoordinate.truncatedVisiblePrefixRemainder_three_eq_rawCoefficient_suffix_mod_blockBase_cu" in carry_doc
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_three" in carry_doc
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_le_seventy_four" in carry_doc
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_one_iff_quotientQ_ge_seventy_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_one" in carry_doc
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_two" in carry_doc
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_le_two" in carry_doc
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_two_iff_quotientQ_ge_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.isMinimalLookaheadCertificate" in carry_doc
    assert "BlockCoordinate.minimalLookaheadCertificate_eight_selector_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.StateAlignmentCertifiedConflict" in carry_doc
    assert "reusable record-shaped payload for certified hidden coefficient conflicts" in carry_doc.replace("\n", " ")
    assert "BlockCoordinate.StateAlignmentCertifiedConflict.not_remainderToCoefficientFunctional" in carry_doc
    assert "BlockCoordinate.StateAlignmentCertifiedConflict.not_remainderToCoefficientFactorsThrough" in carry_doc
    assert "FactorsThrough.eq_of_obs_eq" in carry_doc
    assert "not_factorsThrough_of_collision" in carry_doc
    assert "List.functionalOnFst_iff_factorsThrough_memberSubtype" in carry_doc
    assert "BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_iff_factorsThrough_memberSubtype" in carry_doc
    assert "BlockCoordinate.stateAlignments_not_remainderToCoefficientFactorsThrough_of_not_remainderToCoefficientFunctional" in carry_doc
    assert "BlockCoordinate.StateAlignmentCertifiedConflict.carriedOutput_eq" in carry_doc
    assert "BlockCoordinate.StateAlignmentCertifiedConflict.output_agreement" in carry_doc
    assert "without manual record unpacking" in carry_doc.replace("\n", " ")
    assert "OBSERVABILITY_BOUNDARY.md" in carry_doc
    assert "coefficient information loss across carry-propagated block normalization" in carry_doc.replace("\n", " ")
    assert "same observed remainder state can coexist with unequal raw coefficients while the carried output agrees" in carry_doc.replace("\n", " ")
    assert "working research frame, not a registry claim" in carry_doc.replace("\n", " ")
    assert "BlockCoordinate.stateAlignmentsOneFiveCertifiedVisibilityObstruction" in carry_doc
    assert "BlockCoordinate.stateAlignments_one_five_certifiedConflict_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "BlockCoordinate.stateAlignmentsOneFiveCertifiedVisibilityObstruction_of_lookaheadCertificate" in carry_doc
    assert "BlockCoordinate.minimalLookaheadCertificate_eight_selector_certifiedVisibilityObstruction_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in carry_doc
    assert "QRTour.Composite68.coordinate_stateAlignments_one_five_certifiedConflict_eight_one" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_one_five_certifiedConflict_eight_one" in carry_doc
    assert "share that compact record payload explicitly" in carry_doc.replace("\n", " ")
    assert "QRTour.Composite68.coordinate_minimalLookaheadCertificate_selector_certifiedVisibilityObstruction_eight_one" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_minimalLookaheadCertificate_selector_certifiedVisibilityObstruction_eight_one" in carry_doc
    assert "selected minimal certified lookahead still exposes the certified hidden coefficient conflict" in carry_doc.replace("\n", " ")
    assert "minimal certified lookahead is `1`, and that minimal window still exposes the certified hidden coefficient conflict" in carry_doc.replace("\n", " ")
    assert "QRTour.Composite68.coordinate_lookaheadCertificate_eight_two" in carry_doc
    assert "QRTour.Composite68.coordinate_lookaheadCertificate_eight_three" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_lookaheadCertificate_eight_two" in carry_doc
    assert "QRTour.Composite68Base30.coordinate_lookaheadCertificate_eight_three" in carry_doc
    assert "q ≥ 75" in carry_doc
    assert "q ≥ 3" in carry_doc
    assert "q = 1" in carry_doc
    assert "q = 2" in carry_doc
    assert "`1088`" in carry_doc
    assert "`432`" in carry_doc
    assert "`8/0` never certifies" in carry_doc
    assert "`8/1` certifies exactly when `q ≥ 75`" in carry_doc
    assert "`8/2` exactly" in carry_doc
    assert "lookaheadCertificateHolds 8 2" in carry_doc
    assert "lookaheadCertificateHolds 8 3" in carry_doc
    assert "q = 74" in carry_doc
    assert "B = 5036" in carry_doc
    assert "positive fixed-window lookahead staircase" in carry_doc.replace("\n", " ")
    assert "fixed-window minimal-lookahead classification only" in carry_doc.replace("\n", " ")
    assert "`q ≥ 75 -> L = 1`, `3 ≤ q < 75 -> L = 2`, and `q = 1 or q = 2 -> L = 3`" in carry_doc.replace("\n", " ")
    assert "not a global `small_k_visibility_threshold` theorem" in carry_doc.replace("\n", " ")
    assert "not `carry_dfa_factorization`, and not a new atlas claim" in carry_doc.replace("\n", " ")
    assert "externally certified as `0` and `60`" in carry_doc.replace("\n", " ")
    assert "this proves finite carry-state preservation and the finite hidden-coefficient obstruction for all extra lookahead in the family" in carry_doc.replace("\n", " ")
    assert "not `small_k_visibility_threshold` or `carry_dfa_factorization`" in carry_doc.replace("\n", " ")
    assert "whole `N = 68`, `B ≡ 4 (mod 68)` coordinate family" in carry_doc.replace("\n", " ")
    assert "certified positive-lookahead and hidden-output shape rows empirically" in carry_doc.replace("\n", " ")
    assert "Instrument Atlas" in carry_doc
    assert "search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in carry_doc

    assert "## Empirical Obstruction Hooks" in theorem_guide
    assert "QRTour.Composite68" in theorem_guide
    assert "coordinate_not_coefficientFunctional_eight_one" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_not_coefficientFunctional_eight_one" in theorem_guide
    assert "BlockCoordinate.not_coefficientFunctional_one_five_of_remainderK_eq_four" in theorem_guide
    assert "(base, N, m, B, q, k, L, gap) = (10, 68, 4, 10000, 147, 4, 1, 6208)" in theorem_guide
    assert "(base, N, m, B, q, k, L, gap) = (30, 68, 3, 27000, 397, 4, 1, 10208)" in theorem_guide
    assert "raw coefficients `1588` and `406528`" in theorem_guide
    assert "search-reptends visibility-coefficient-conflict-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in theorem_guide
    assert "search-reptends visibility-coefficient-conflict-families --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in theorem_guide
    assert "search-reptends visibility-composite68-base-sweep --max-base 120 --blocks 8 --top 20" in theorem_guide
    assert "search-reptends visibility-composite68-congruence-family --max-base 120 --max-m 8 --blocks 8 --top 0" in theorem_guide
    assert "Certificate Workbench" in theorem_guide
    assert "search-reptends visibility-certificate-workbench --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in theorem_guide
    assert "Observability Atlas" in theorem_guide
    assert "`hidden_coefficient_conflict`, `visible_coefficient_conflict`, `coefficient_functional_frontier`, and `gap_one_bridge_candidate`" in theorem_guide
    assert "Observability Instrument Compare" in theorem_guide
    assert "`observability_source_symmetry_shape` plus `observability_instrument_member` rows" in theorem_guide
    assert "Shape17/K4 family classifier" in theorem_guide
    assert "`observability_shape17_k4_family_summary` plus `observability_shape17_k4_family_member` rows" in theorem_guide
    assert "empirical/open-boundary certificate tooling" in theorem_guide
    assert "not as a promoted theorem surface, new theorem-witness record, or atlas claim" in theorem_guide
    assert "search-reptends visibility-certificate-lean-fixtures --max 1200 --bases 7,10,12,30 --blocks 8" in theorem_guide
    assert "certificate-lean-fixtures-v1" in theorem_guide
    assert "copyable_lean_stub" in theorem_guide
    assert "search-reptends visibility-certificate-lean-stubs --max 1200 --bases 7,10,12,30 --blocks 8" in theorem_guide
    assert "certificate-lean-stubs-v1" in theorem_guide
    assert "certificate-fixture-mapping-lint-v1" in theorem_guide
    assert "source_pinning_recipe" in theorem_guide
    assert "repeatable path from lint output to Lean theorem names" in theorem_guide
    assert "search-reptends visibility-certificate-lean-stubs --max 120 --bases 7,10,12,30 --blocks 8 --first-scaffold-only" in theorem_guide
    assert "QRTour.FutureBase30N7" in theorem_guide
    assert "QRTour.FutureBase30N14" in theorem_guide
    assert "QRTour.FutureBase30N28" in theorem_guide
    assert "QRTour.FutureBase12N10" in theorem_guide
    assert "QRTour.FutureBase10N102" in theorem_guide
    assert "QRTour.FutureBase7N5" in theorem_guide
    assert "QRTour.FutureBase12N5" in theorem_guide
    assert "QRTour.FutureBase30N34" in theorem_guide
    assert "QRTour.FutureBase7N93" in theorem_guide
    assert "QRTour.FutureBase10N39" in theorem_guide
    assert "QRTour.FutureBase10N78" in theorem_guide
    assert "QRTour.FutureBase10N96" in theorem_guide
    assert "QRTour.FutureBase12N35" in theorem_guide
    assert "QRTour.FutureBase12N31" in theorem_guide
    assert "lean_package_plan" in theorem_guide
    assert "coordinate_stateAlignments_zero_three_certifiedConflict_eight_two" in theorem_guide
    assert "base30_n7_m1_blocks8_L2_not_remainderToCoefficientFunctional" in theorem_guide
    assert "coordinate_stateAlignments_one_four_certifiedConflict_eight_two" in theorem_guide
    assert "base30_n14_m1_blocks8_L2_not_remainderToCoefficientFunctional" in theorem_guide
    assert "coordinate_stateAlignments_two_five_certifiedConflict_eight_two" in theorem_guide
    assert "base30_n28_m1_blocks8_L2_not_remainderToCoefficientFunctional" in theorem_guide
    assert "coordinate_stateAlignments_one_five_certifiedConflict_eight_three" in theorem_guide
    assert "base12_n10_m1_blocks8_L3_not_remainderToCoefficientFunctional" in theorem_guide
    assert "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one" in theorem_guide
    assert "base10_n102_m4_blocks8_L1_not_remainderToCoefficientFunctional" in theorem_guide
    assert "coordinate_stateAlignments_zero_four_certifiedConflict_eight_five" in theorem_guide
    assert "base7_n5_m1_blocks8_L5_not_remainderToCoefficientFunctional" in theorem_guide
    assert "coordinate_stateAlignments_zero_four_certifiedConflict_eight_four" in theorem_guide
    assert "base12_n5_m1_blocks8_L4_not_remainderToCoefficientFunctional" in theorem_guide
    assert "base30_n34_m3_blocks8_L1_not_remainderToCoefficientFunctional" in theorem_guide
    assert "base7_n93_m6_blocks8_L1_not_remainderToCoefficientFunctional" in theorem_guide
    assert "base10_n39_m5_blocks8_L1_not_remainderToCoefficientFunctional" in theorem_guide
    assert "base10_n78_m5_blocks8_L1_not_remainderToCoefficientFunctional" in theorem_guide
    assert "base10_n96_m2_blocks8_L3_not_remainderToCoefficientFunctional" in theorem_guide
    assert "base12_n35_m2_blocks8_L3_not_remainderToCoefficientFunctional" in theorem_guide
    assert "base12_n31_m6_blocks8_L1_not_remainderToCoefficientFunctional" in theorem_guide
    assert "source-ready" in theorem_guide
    assert "`--namespace` mapping-lint mode" in theorem_guide
    assert "stub scaffold/lint command" in theorem_guide
    assert "not as an automatic Lean-file writer or claim promotion path" in theorem_guide
    assert "empirical/open-boundary certificate-to-Lean tooling" in theorem_guide
    assert "not as a theorem surface, registry promotion, theorem-witness record, or atlas claim" in theorem_guide
    assert "periodic_modulus=17;k=4;remainder_state=4;positions=[1, 5];carry_states=[0, 60];output_hidden=true" in theorem_guide
    assert "classify_composite68_cross_base_hidden_output_conflict" in theorem_guide
    assert "`10, 30, 32, 64, 66, 72, 98, 100`" in theorem_guide
    assert "`B mod 68 = 4`" in theorem_guide
    assert "4^1 ≡ 4^5 (mod 68)" in theorem_guide
    assert "B ≡ 4 (mod 68)" in theorem_guide
    assert "The finite Lean response has now landed" in theorem_guide
    assert "remaining open boundary is arithmetic classification" in theorem_guide
    assert "BlockCoordinate.stateAlignments_remainderIn_one_eq_five_of_modulus_eq_sixty_eight" in theorem_guide
    assert "BlockCoordinate.not_coefficientFunctional_one_five_of_modulus_eq_sixty_eight" in theorem_guide
    assert "BlockCoordinate.remainderK_eq_four_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.not_coefficientFunctional_one_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.incomingCarry_one_eq_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.incomingCarry_five_eq_sixty_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.incomingCarry_hiddenOutput_one_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "QRTour.Composite68.coordinate_incomingCarry_hiddenOutput_one_five" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_incomingCarry_hiddenOutput_one_five" in theorem_guide
    assert "BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "composite68_suffixCarry_five_eq_sixty_of_tailCarry_le_nine_hundred_sixty_three" in theorem_guide
    assert "composite68_suffixCarry_one_eq_zero_of_tailCarry_le_nine_hundred_sixty_three" in theorem_guide
    assert "BlockCoordinate.incomingCarry_step_recurrence" in theorem_guide
    assert "BlockCoordinate.traceRawWord_carryIn_le_incomingCarry" in theorem_guide
    assert "BlockCoordinate.visibleCarryTrace_carryIn_le_incomingCarry" in theorem_guide
    assert "BlockCoordinate.stateAlignments_carryIn_le_incomingCarry" in theorem_guide
    assert "BlockCoordinate.incomingCarry_seven_eq_nine_hundred_sixty_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_any_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_of_carry_states_zero_sixty" in theorem_guide
    assert "QRTour.Composite68.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry" in theorem_guide
    assert "QRTour.Composite68.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero" in theorem_guide
    assert "fixed-window trace arithmetic" in theorem_guide
    assert "the `8/1` `stateAlignments` trace itself supplies the `(0, 60)` finite carry-state certificate" in theorem_guide
    assert "the `8/0` `stateAlignments` trace already supplies the same `(0, 60)` finite carry-state certificate" in theorem_guide
    assert "positive lookahead is still used for the certified output-agreement obstruction window" in theorem_guide
    assert "finite carry entering the `4^7` block is at most `963`" in theorem_guide
    assert "Lean proves every finite carry entering the `4^7` block is at most `963`" in theorem_guide
    assert "every `8/L` state-alignment window in that family realizes the canonical `0` and `60` incoming carries" in theorem_guide
    assert "not output agreement, `small_k_visibility_threshold`, or `carry_dfa_factorization`" in theorem_guide
    assert "obstruction-first finite visibility theorem" in theorem_guide
    assert "BlockCoordinate.stateAlignments_one_five_hiddenCoefficientConflict_eight_any_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.stateAlignments_one_five_certifiedVisibilityObstruction_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "QRTour.Composite68.coordinate_stateAlignments_one_five_hiddenCoefficientConflict_eight_one" in theorem_guide
    assert "QRTour.Composite68.coordinate_stateAlignments_one_five_certifiedVisibilityObstruction_eight_one" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_one_five_hiddenCoefficientConflict_eight_one" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_one_five_certifiedVisibilityObstruction_eight_one" in theorem_guide
    assert "lookaheadCertificateHolds 8 L" in theorem_guide
    assert "not a closure of `small_k_visibility_threshold` or `carry_dfa_factorization`" in theorem_guide
    assert "BlockCoordinate.truncatedVisiblePrefixRemainder_one_eq_rawCoefficient_mod_blockBase" in theorem_guide
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_seventy_five" in theorem_guide
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_seventy_four" in theorem_guide
    assert "BlockCoordinate.truncatedVisiblePrefixRemainder_two_eq_rawCoefficient_suffix_mod_blockBase_sq" in theorem_guide
    assert "BlockCoordinate.truncatedVisiblePrefixRemainder_three_eq_rawCoefficient_suffix_mod_blockBase_cu" in theorem_guide
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_three" in theorem_guide
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_le_seventy_four" in theorem_guide
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_one_iff_quotientQ_ge_seventy_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_one" in theorem_guide
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_two" in theorem_guide
    assert "BlockCoordinate.not_lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_le_two" in theorem_guide
    assert "BlockCoordinate.lookaheadCertificateHolds_eight_two_iff_quotientQ_ge_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.isMinimalLookaheadCertificate" in theorem_guide
    assert "BlockCoordinate.isMinimalLookaheadCertificate_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_seventy_five" in theorem_guide
    assert "BlockCoordinate.isMinimalLookaheadCertificate_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_three_and_lt_seventy_five" in theorem_guide
    assert "BlockCoordinate.isMinimalLookaheadCertificate_eight_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_one_or_two" in theorem_guide
    assert "BlockCoordinate.minimalLookaheadCertificate_eight_selector_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.StateAlignmentCertifiedConflict" in theorem_guide
    assert "reusable record-shaped payload for certified hidden coefficient conflicts" in theorem_guide.replace("\n", " ")
    assert "BlockCoordinate.StateAlignmentCertifiedConflict.not_remainderToCoefficientFunctional" in theorem_guide
    assert "BlockCoordinate.StateAlignmentCertifiedConflict.not_remainderToCoefficientFactorsThrough" in theorem_guide
    assert "FactorsThrough.eq_of_obs_eq" in theorem_guide
    assert "not_factorsThrough_of_collision" in theorem_guide
    assert "List.functionalOnFst_iff_factorsThrough_memberSubtype" in theorem_guide
    assert "BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_iff_factorsThrough_memberSubtype" in theorem_guide
    assert "BlockCoordinate.stateAlignments_not_remainderToCoefficientFactorsThrough_of_not_remainderToCoefficientFunctional" in theorem_guide
    assert "BlockCoordinate.StateAlignmentCertifiedConflict.carriedOutput_eq" in theorem_guide
    assert "BlockCoordinate.StateAlignmentCertifiedConflict.output_agreement" in theorem_guide
    assert "without manual record unpacking" in theorem_guide.replace("\n", " ")
    assert "OBSERVABILITY_BOUNDARY.md" in theorem_guide
    assert "coefficient information loss across carry-propagated block normalization" in theorem_guide.replace("\n", " ")
    assert "same observed remainder state can coexist with unequal raw coefficients while the carried output agrees" in theorem_guide.replace("\n", " ")
    assert "working research frame, not a registry claim" in theorem_guide.replace("\n", " ")
    assert "Recommended obstruction-record proof path" in theorem_guide
    assert "family wrapper -> record -> projection accessor" in theorem_guide
    assert "minimal cross-base proof-style exemplars" in theorem_guide
    assert "Copyable three-line obstruction-record proof pattern" in theorem_guide
    assert "have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_one" in theorem_guide
    assert "have hnonfunctional := hrecord.not_remainderToCoefficientFunctional" in theorem_guide
    assert "have hfactor := hrecord.not_remainderToCoefficientFactorsThrough" in theorem_guide
    assert "have hwindow := coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one" in theorem_guide
    assert "exact hnonfunctional" in theorem_guide
    assert "exact hfactor" in theorem_guide
    assert "full-window factor-through obstruction variant" in theorem_guide
    assert "replace the first line with a direct call" in theorem_guide
    assert "Record accessor map" in theorem_guide
    assert "Desired conclusion" in theorem_guide
    assert "Nonfunctional remainder-to-coefficient mapping" in theorem_guide
    assert "Factor-through obstruction" in theorem_guide
    assert "Full-window factor-through obstruction" in theorem_guide
    assert "Hidden carried-output equality" in theorem_guide
    assert "Certified output agreement" in theorem_guide
    assert "`¬ List.FunctionalOnFst` for the observed `(remainderIn, coefficient)` map" in theorem_guide
    assert "`¬ FactorsThrough` for the two-point remainder-observation to coefficient-signal readout" in theorem_guide
    assert "`¬ FactorsThrough` for the complete finite state-alignment member subtype readout" in theorem_guide
    assert "Equal `carryBlockValue` on the two conflicting rows" in theorem_guide
    assert "Both conflicting rows have `carryBlockValue = remainderBlockValue`" in theorem_guide
    assert "QRTour.Composite68.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one" in theorem_guide
    assert "QRTour.Composite68.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_eight_one" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_eight_one" in theorem_guide
    assert "QRTour.Composite68.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one" in theorem_guide
    assert ".not_remainderToCoefficientFunctional" in theorem_guide
    assert ".not_remainderToCoefficientFactorsThrough" in theorem_guide
    assert ".carriedOutput_eq" in theorem_guide
    assert ".output_agreement" in theorem_guide
    assert "BlockCoordinate.stateAlignmentsOneFiveCertifiedVisibilityObstruction" in theorem_guide
    assert "BlockCoordinate.stateAlignments_one_five_certifiedConflict_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "BlockCoordinate.stateAlignmentsOneFiveCertifiedVisibilityObstruction_of_lookaheadCertificate" in theorem_guide
    assert "BlockCoordinate.minimalLookaheadCertificate_eight_selector_certifiedVisibilityObstruction_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four" in theorem_guide
    assert "QRTour.Composite68.coordinate_stateAlignments_one_five_certifiedConflict_eight_one" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_stateAlignments_one_five_certifiedConflict_eight_one" in theorem_guide
    assert "share that compact record payload explicitly" in theorem_guide.replace("\n", " ")
    assert "QRTour.Composite68.coordinate_minimalLookaheadCertificate_selector_certifiedVisibilityObstruction_eight_one" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_minimalLookaheadCertificate_selector_certifiedVisibilityObstruction_eight_one" in theorem_guide
    assert "minimal selected certified lookahead still exposes the certified hidden coefficient conflict" in theorem_guide.replace("\n", " ")
    assert "minimal certified lookahead is `1`, and that minimal window still exposes the certified hidden coefficient conflict" in theorem_guide.replace("\n", " ")
    assert "QRTour.Composite68.coordinate_lookaheadCertificate_eight_two" in theorem_guide
    assert "QRTour.Composite68.coordinate_lookaheadCertificate_eight_three" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_lookaheadCertificate_eight_two" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_lookaheadCertificate_eight_three" in theorem_guide
    assert "QRTour.Composite68.coordinate_quotientQ_ge_seventy_five" in theorem_guide
    assert "QRTour.Composite68Base30.coordinate_quotientQ_ge_seventy_five" in theorem_guide
    assert "`q ≥ 75` implies `lookaheadCertificateHolds 8 1`" in theorem_guide
    assert "`q ≥ 3` implies `lookaheadCertificateHolds 8 2`" in theorem_guide
    assert "every good coordinate in that family satisfies `lookaheadCertificateHolds 8 3`" in theorem_guide
    assert "`8/0` never certifies" in theorem_guide
    assert "`8/1` exactly when `q ≥ 75`" in theorem_guide
    assert "`8/2` exactly when `q ≥ 3`" in theorem_guide
    assert "gap numerators `1088` at `q = 1` and `432` at `q = 2`" in theorem_guide
    assert "`q = 74` with `B = 5036`" in theorem_guide
    assert "not a closed minimal-`L` classification and not a new atlas claim" in theorem_guide
    assert "positive fixed-window lookahead staircase" in theorem_guide
    assert "not a closed global minimal-`L` theorem or an atlas-status change" in theorem_guide
    assert "fixed-window minimal-lookahead classification" in theorem_guide
    assert "`q ≥ 75 -> L = 1`, `3 ≤ q < 75 -> L = 2`, and `q = 1` or `q = 2 -> L = 3`" in theorem_guide
    assert "not a global theorem or atlas-status change" in theorem_guide
    assert "externally certified as `0` and `60`" in theorem_guide
    assert "output/certificate classification" in theorem_guide
    assert "whole `N = 68`, `B ≡ 4 (mod 68)` coordinate family" in theorem_guide
    assert "certified positive-lookahead and hidden-output shape classifier remains empirical bounded evidence" in theorem_guide
    assert "`small_k_visibility_threshold` and `carry_dfa_factorization`" in theorem_guide

    assert "Visibility Optics" in roadmap
    assert "source remainder orbit" in roadmap
    assert "finite carry window" in roadmap
    assert "Instrument Atlas" in roadmap
    assert "working-axiom pressure" in roadmap
    assert "VISIBILITY_GEOMETRY.md" in roadmap
    assert "GeometricStack" in roadmap
    assert "CHART_INVARIANCE.md" in roadmap
    assert "clean chart distortion witnesses" in roadmap.replace("\n  ", " ")
    assert "ChartObservation` rows project to `ChartSignature`s" in roadmap
    assert "compact witness counts are" in roadmap
    assert "state-map labels remain annotated beneath" in roadmap

    assert "OrbitInstrumentVisibilityGallery" in site_document
    assert "Orbit, Instrument, Visibility" in gallery
    assert "The reptend is the observed trace; the remainder orbit is the source;" in gallery
    assert "finite carry window is the instrument" in gallery
    assert "Visibility Optics" in gallery
    assert "remainder orbit" in gallery
    assert "raw coefficient stream" in gallery
    assert "carry-propagated block normalization" in gallery
    assert "finite-window trace" in gallery
    assert "search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996" in gallery
    assert "Visibility Optics workbench" in gallery
    assert "search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20" in gallery
    assert "search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20" in gallery
    assert "search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in gallery
    assert "base-instrument comparison" in gallery
    assert "Instrument Atlas" in gallery
    assert "docs/INSTRUMENT_ATLAS.md" in gallery
    assert "Visibility Geometry" in gallery
    assert "docs/VISIBILITY_GEOMETRY.md" in gallery
    assert "Chart Invariance" in gallery
    assert "docs/CHART_INVARIANCE.md" in gallery
    assert "search-reptends chart-invariance --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in gallery
    assert "phase space" in gallery
    assert "capacity thresholds" in gallery
    assert "docs/OUTSIDE_READER_DOORWAY.md" in gallery
    assert "docs/ORBIT_INSTRUMENT_VISIBILITY.md" in gallery
    assert "docs/CARRY_TRANSDUCER.md" in gallery
    assert "docs/VISIBILITY_OPTICS_WORKBENCH.md" in gallery
    assert "carry_dfa_factorization" in gallery
    assert "small_k_visibility_threshold" in gallery


def test_carry_and_visibility_status_anchor_blocks_match_registry_data() -> None:
    assert _normalize_repo_link_targets(
        _extract_block(
            CARRY_TRANSDUCER.read_text(),
            "<!-- CARRY_TRANSDUCER_STATUS_ANCHOR_START -->",
            "<!-- CARRY_TRANSDUCER_STATUS_ANCHOR_END -->",
        )
    ) == _normalize_repo_link_targets(list(render_carry_transducer_status_anchor_lines()))

    assert _normalize_repo_link_targets(
        _extract_block(
            CARRIED_PREFIX_VISIBILITY.read_text(),
            "<!-- CARRIED_PREFIX_VISIBILITY_STATUS_ANCHOR_START -->",
            "<!-- CARRIED_PREFIX_VISIBILITY_STATUS_ANCHOR_END -->",
        )
    ) == _normalize_repo_link_targets(list(render_carried_prefix_visibility_status_anchor_lines()))
    assert _normalize_repo_link_targets(
        _extract_block(
            CARRY_TRANSDUCER.read_text(),
            "<!-- CARRY_TRANSDUCER_THROUGHLINE_START -->",
            "<!-- CARRY_TRANSDUCER_THROUGHLINE_END -->",
        )
    ) == _normalize_repo_link_targets(list(render_throughline_witness_ladder_lines()))


def test_throughline_blocks_keep_carry_factorization_open_and_thesis_framed() -> None:
    readme_text = README.read_text()
    witness_text = WITNESS_ATLAS.read_text()

    for text in (readme_text, witness_text):
        assert "`carry_dfa_factorization`" in text
        assert "`open`" in text
        assert "research-thesis" in text
        assert "`orbit_plus_carry_factorization`" in text
        assert "preimage-fiber profile" in text
        assert "Claim ID `orbit_plus_carry_factorization`" not in text

    thesis_block = _extract_block(
        readme_text,
        "<!-- THROUGHLINE_RESEARCH_THESIS_START -->",
        "<!-- THROUGHLINE_RESEARCH_THESIS_END -->",
    )
    assert any("research-thesis" in line for line in thesis_block)
    assert any("remains `open` under `carry_dfa_factorization`" in line for line in thesis_block)


def test_theorem_guide_mentions_factorization_frontier_support_honestly() -> None:
    text = LEAN_GUIDE.read_text()

    assert "factorization-frontier support" in text
    assert "QRTour/Factorization.lean" in text
    assert "preimage-fiber profile (state-merging atlas)" in text


def test_research_brief_and_observability_problem_ledger_stay_status_honest() -> None:
    readme = README.read_text()
    brief = RESEARCH_BRIEF.read_text()
    normalized_brief = brief.replace("\n", " ")
    observability = OBSERVABILITY_BOUNDARY.read_text()
    ledger = OBSERVABILITY_PROBLEMS.read_text()
    normalized_ledger = ledger.replace("\n", " ")

    assert "docs/OBSERVABILITY_PROBLEMS.md" in readme
    assert "explicit stop conditions" in readme

    assert brief.startswith("# Research Brief v0.2: Orbit, Carry, and Observability")
    assert "Positional notation is an observation instrument for arithmetic dynamics" in brief
    assert "1/N = q/(B-k) = (q/B) * 1/(1-k/B) = Σ q*k^j / B^(j+1)" in brief
    assert "FactorsThrough(obs, signal)" in brief
    assert "hidden coefficient conflict" in brief
    assert "Positive reconstruction" in brief
    assert "finite_remainder_power_residue_no_collision" in brief
    assert "finite_remainder_power_residue_no_wrap" in brief
    assert "BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_pow_lt_modulus" in brief
    assert "QRTour.FutureBase7N170.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in brief
    assert "QRTour.FutureBase12N149.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in brief
    assert "(12, 289, 5, 248832, 861, 3, 1, 74115)" in brief
    assert (
        "QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in brief
    )
    assert "(10, 641, 5, 100000, 156, 4, 1, 76384)" in brief
    assert (
        "QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in brief
    )
    assert "(10, 361, 5, 100000, 277, 3, 1, 82603)" in brief
    assert "(7, 340, 3, 343, 1, 3, 1, 299)" in brief
    assert "[1, 3, 9, 27, 81, 243, 49, 147]" in brief
    assert "same-base/block-remainder family criterion" in normalized_brief
    assert "`small_k_visibility_threshold`" in brief
    assert "`carry_dfa_factorization`" in brief
    assert "They are not global morphism" in brief
    assert "OBSERVABILITY_PROBLEMS.md" in brief
    assert "Recommended review packet" in brief

    assert "OBSERVABILITY_PROBLEMS.md" in observability
    assert "positive reconstruction, target-lattice separations" in observability
    assert "explicit Lean/export surfaces and stop conditions" in observability

    assert ledger.startswith("# Observability Problems Ledger")
    assert "not a proof-status atlas and not a registry surface" in normalized_ledger
    assert "`small_k_visibility_threshold` and `carry_dfa_factorization`" in ledger
    assert "## P1. Positive Reconstruction Criterion" in ledger
    assert "## P2. Observability Target Lattice" in ledger
    assert "## P3. Base As Observation Instrument" in ledger
    assert "## P4. Carry Normalizer As Rational Transduction" in ledger
    assert "## P5. Quantitative Observability Margins" in ledger
    assert "finite_remainder_power_residue_no_collision" in ledger
    assert "finite_remainder_power_residue_no_wrap" in ledger
    assert "remainder_power_residue_window" in ledger
    assert "remainder_power_unreduced_window" in ledger
    assert "first_unpinned_positive_reconstruction_tuple" in ledger
    assert "first_unpinned_positive_reconstruction_family_seed_tuples" in ledger
    assert "(7, 340, 3, 343, 1, 3, 1, 299)" in ledger
    assert "first_uncovered_positive_reconstruction_tuple" in ledger
    assert "QRTour.FutureBase10N997.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in ledger
    assert (
        "QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base30K3PositiveReconstruction.n299_n897_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "(10, 498, 3, 1000, 2, 4, 1, 928)" in ledger
    assert (
        "QRTour.Base10K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base10K4PositiveReconstruction.n498_n996_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "(12, 575, 3, 1728, 3, 3, 1, 1053)" in ledger
    assert "[1, 3, 9, 27, 81, 243, 154, 462]" in ledger
    assert "QRTour.FutureBase12N575.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(12, 75, 3, 1728, 23, 3, 1, 1161)" in ledger
    assert "[1, 3, 9, 27, 6, 18, 54, 12]" in ledger
    assert (
        "QRTour.Base12K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12K3PositiveReconstruction.n75_n575_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "[23, 25, 69, 75, 115, 345, 575, 1725]" in ledger
    assert "(7, 1199, 4, 2401, 2, 3, 1, 1284)" in ledger
    assert "[1, 3, 9, 27, 81, 243, 729, 988]" in ledger
    assert "QRTour.FutureBase7N1199.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(10, 294, 4, 10000, 34, 4, 1, 1776)" in ledger
    assert "[1, 4, 16, 64, 256, 142, 274, 214]" in ledger
    assert "QRTour.FutureBase10N294.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(7, 109, 4, 2401, 22, 3, 1, 2119)" in ledger
    assert "[1, 3, 9, 27, 81, 25, 75, 7]" in ledger
    assert (
        "QRTour.Base7Stride4K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base7Stride4K3PositiveReconstruction.n109_n1199_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "[109, 218, 1199, 2398]" in ledger
    assert "[1, 2, 11, 22]" in ledger
    assert "(7, 46, 2, 49, 1, 3, 2, 2171)" in ledger
    assert "[1, 3, 9, 27, 35, 13, 39, 25]" in ledger
    assert "QRTour.FutureBase7N46.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
        in ledger
    )
    assert (
        "QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        in ledger
    )
    assert "(7, 141, 4, 2401, 17, 4, 1, 2353)" in ledger
    assert "[1, 4, 16, 64, 115, 37, 7, 28]" in ledger
    assert "QRTour.FutureBase7N141.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(10, 714, 4, 10000, 14, 4, 1, 2496)" in ledger
    assert "[1, 4, 16, 64, 256, 310, 526, 676]" in ledger
    assert (
        "QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base10Stride4K4PositiveReconstruction.n294_n714_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "[49, 98, 119, 147, 196, 238, 294, 357, 476, 588, 714, 833]" in ledger
    assert "(12, 146, 4, 20736, 142, 4, 1, 4352)" in ledger
    assert "[1, 4, 16, 64, 110, 2, 8, 32]" in ledger
    assert "QRTour.FutureBase12N146.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(10, 769, 4, 10000, 13, 3, 1, 4707)" in ledger
    assert "[1, 3, 9, 27, 81, 243, 729, 649]" in ledger
    assert "QRTour.FutureBase10N769.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(7, 345, 6, 117649, 341, 4, 1, 5534)" in ledger
    assert "[1, 4, 16, 64, 256, 334, 301, 169]" in ledger
    assert "QRTour.FutureBase7N345.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(7, 465, 6, 117649, 253, 4, 1, 7901)" in ledger
    assert "[1, 4, 16, 64, 256, 94, 376, 109]" in ledger
    assert (
        "QRTour.Base7Stride6K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert "(7, 542, 5, 16807, 31, 5, 1, 8472)" in ledger
    assert "[1, 5, 25, 125, 83, 415, 449, 77]" in ledger
    assert "QRTour.FutureBase7N542.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(12, 73, 4, 20736, 284, 4, 1, 8704)" in ledger
    assert "[1, 4, 16, 64, 37, 2, 8, 32]" in ledger
    assert (
        "QRTour.Base12Stride4K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12Stride4K4PositiveReconstruction.n73_n146_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "[71, 73, 142, 146, 284, 292, 5183, 10366, 20732]" in ledger
    assert "(12, 47, 2, 144, 3, 3, 2, 9639)" in ledger
    assert "[1, 3, 9, 27, 34, 8, 24, 25]" in ledger
    assert "QRTour.FutureBase12N47.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
        in ledger
    )
    assert (
        "QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        in ledger
    )
    assert "(12, 141, 2, 144, 1, 3, 2, 10125)" in ledger
    assert "[1, 3, 9, 27, 81, 102, 24, 72]" in ledger
    assert (
        "QRTour.Base12Stride2K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12Stride2K3PositiveReconstruction.n47_n141_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "[47, 141]" in ledger
    assert "(30, 794, 3, 27000, 34, 4, 1, 12776)" in ledger
    assert "[1, 4, 16, 64, 256, 230, 126, 504]" in ledger
    assert "QRTour.FutureBase30N794.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(7, 113, 3, 343, 3, 4, 2, 13444)" in ledger
    assert "[1, 4, 16, 64, 30, 7, 28, 112]" in ledger
    assert "QRTour.FutureBase7N113.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
        in ledger
    )
    assert (
        "QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        in ledger
    )
    assert "(12, 691, 4, 20736, 30, 6, 1, 20736)" in ledger
    assert "[1, 6, 36, 216, 605, 175, 359, 81]" in ledger
    assert "QRTour.FutureBase12N691.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(30, 397, 3, 27000, 68, 4, 1, 25552)" in ledger
    assert "[1, 4, 16, 64, 256, 230, 126, 107]" in ledger
    assert (
        "QRTour.Base30Stride3K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base30Stride3K4PositiveReconstruction.n397_n794_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "[397, 794, 1588, 6749, 13498, 26996]" in ledger
    assert "[1, 2, 4, 17, 34, 68]" in ledger
    assert "(10, 578, 5, 100000, 173, 6, 1, 26432)" in ledger
    assert "[1, 6, 36, 216, 140, 262, 416, 184]" in ledger
    assert "QRTour.FutureBase10N578.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(10, 277, 5, 100000, 361, 3, 1, 31479)" in ledger
    assert "[1, 3, 9, 27, 81, 243, 175, 248]" in ledger
    assert "QRTour.FutureBase10N277.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(7, 669, 7, 823543, 1231, 4, 1, 32398)" in ledger
    assert "[1, 4, 16, 64, 256, 355, 82, 328]" in ledger
    assert "QRTour.FutureBase7N669.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(7, 71, 6, 117649, 1657, 2, 1, 46404)" in ledger
    assert "[1, 2, 4, 8, 16, 32, 64, 57]" in ledger
    assert "QRTour.FutureBase7N71.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(7, 118, 6, 117649, 997, 3, 1, 47027)" in ledger
    assert "[1, 3, 9, 27, 81, 7, 21, 63]" in ledger
    assert "QRTour.FutureBase7N118.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
        in ledger
    )
    assert (
        "QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(7, 997, 6, 117649, 118, 3, 1, 49345)" in ledger
    assert "[1, 3, 9, 27, 81, 243, 729, 193]" in ledger
    assert (
        "QRTour.Base7Stride6K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base7Stride6K3PositiveReconstruction.n118_n997_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "[59, 118, 997, 1994, 58823, 117646]" in ledger
    assert "(10, 289, 5, 100000, 346, 6, 1, 52864)" in ledger
    assert "[1, 6, 36, 216, 140, 262, 127, 184]" in ledger
    assert "(10, 578, 5, 100000, 173, 6, 1, 26432)" in ledger
    assert (
        "QRTour.Base10Stride5K6PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base10Stride5K6PositiveReconstruction.n289_n578_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "[17, 34, 173, 289, 346, 578, 2941, 5882, 49997, 99994]" in ledger
    assert "(12, 226, 5, 248832, 1101, 6, 1, 62208)" in ledger
    assert "[1, 6, 36, 216, 166, 92, 100, 148]" in ledger
    assert "QRTour.FutureBase12N226.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase12N226.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        in ledger
    )
    assert "(7, 338, 3, 343, 1, 5, 2, 64744)" in ledger
    assert "[1, 5, 25, 125, 287, 83, 77, 47]" in ledger
    assert "QRTour.FutureBase7N338.coordinate_remainderK_powerResidues_nodup_eight" in ledger
    assert (
        "QRTour.FutureBase7N338.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        in ledger
    )
    assert "(12, 149, 5, 248832, 1670, 2, 1, 70144)" in ledger
    assert "[1, 2, 4, 8, 16, 32, 64, 128]" in ledger
    assert "QRTour.FutureBase12N149.coordinate_remainderK_pow_lt_modulus_eight" in ledger
    assert "QRTour.FutureBase12N149.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one" in ledger
    assert "(12, 289, 5, 248832, 861, 3, 1, 74115)" in ledger
    assert "[1, 3, 9, 27, 81, 243, 151, 164]" in ledger
    assert (
        "QRTour.Base12Stride5K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base12Stride5K3PositiveReconstruction.n289_n861_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "(10, 641, 5, 100000, 156, 4, 1, 76384)" in ledger
    assert "[1, 4, 16, 64, 256, 383, 250, 359]" in ledger
    assert (
        "QRTour.Base10Stride5K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base10Stride5K4PositiveReconstruction.n641_n1282_powerResidues_nodup_eight_pair"
        in ledger
    )
    assert "(10, 361, 5, 100000, 277, 3, 1, 82603)" in ledger
    assert "[1, 3, 9, 27, 81, 243, 7, 21]" in ledger
    assert (
        "QRTour.Base7K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
        in ledger
    )
    assert (
        "QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        in ledger
    )
    assert "use_lean_proved_family_criterion_before_source_pinning_more_examples" in ledger
    assert "prove_or_reject_same_base_block_remainder_power_no_collision_family" in ledger
    assert "observability-target-split" in ledger
    assert "observability-instrument-compare" in ledger
    assert "carry-factorization --max 500 --blocks 8" in ledger
    assert "finite factor-through statements first" in ledger
    assert "global transducer claims last" in ledger


def test_track_18_roadmap_marks_release_snapshot_as_landed() -> None:
    text = HARDENING_ROADMAP.read_text()
    track_18 = text.split("## Track 18: Formal-Systems Integration and Release Snapshot", 1)[1].split(
        "## Track 19: Post-Exact Visibility and Finite-Carry Theorem Frontier", 1
    )[0]
    current_state = text.split("## Current State", 1)[1]

    assert "Status: `implemented`" in track_18
    assert "- [x] Add a proof-system legend across the main public surfaces:" in track_18
    assert "- [x] Add a release-snapshot task that packages:" in track_18
    assert "build_release_snapshot.py" in track_18
    assert "docs/RELEASE_SNAPSHOT.md" in track_18
    assert "data/release_snapshot.json" in track_18
    assert "Tracks 1 through 18 are now implemented." in current_state
    assert "release-facing snapshot" in current_state
    assert "finish the release-facing snapshot now that the proof-system legend is" not in current_state


def _extract_block(text: str, start_marker: str, end_marker: str) -> list[str]:
    start = text.index(start_marker) + len(start_marker)
    end = text.index(end_marker)
    return [line.rstrip() for line in text[start:end].strip().splitlines()]


def _normalize_repo_link_targets(lines: list[str]) -> list[str]:
    return [
        re.sub(r"\]\([^)]*quadratic-residue-reptends/", "](REPO_ROOT/", line)
        for line in lines
    ]


def _extract_table_claim_ids(text: str, heading: str) -> set[str]:
    return {
        row[0].strip("`")
        for row in _extract_markdown_table_rows(text, heading)
    }


def _extract_markdown_table_rows(text: str, heading: str) -> list[list[str]]:
    lines = text.splitlines()
    start = lines.index(heading) + 1
    while start < len(lines) and not lines[start].startswith("|"):
        start += 1

    table_lines: list[str] = []
    while start < len(lines) and lines[start].startswith("|"):
        table_lines.append(lines[start])
        start += 1

    return [
        [cell.strip() for cell in row.strip().strip("|").split("|")]
        for row in table_lines[2:]
    ]


def _extract_markdown_link_targets(cell: str) -> list[str]:
    return re.findall(r"\]\(([^)]+)\)", cell)


def _extract_code_ids(cell: str) -> list[str]:
    return re.findall(r"`([^`]+)`", cell)


def _normalize_theorem_guide_lean_targets(targets: list[str]) -> list[str]:
    return [_resolve_theorem_guide_lean_path(target).relative_to(ROOT).as_posix() for target in targets]


def _theorem_guide_open_claim_boundary_modules_by_claim() -> dict[str, set[str]]:
    theorem_guide_text = LEAN_GUIDE.read_text()
    return {
        claim_id_cell.strip("`"): set(
            _normalize_theorem_guide_lean_targets(_extract_markdown_link_targets(boundary_cell))
        )
        for claim_id_cell, boundary_cell in _extract_markdown_table_rows(
            theorem_guide_text, "## Open Claims With Lean Boundary Work"
        )
    }


def _theorem_guide_open_claim_support_modules_by_claim() -> dict[str, set[str]]:
    theorem_guide_text = LEAN_GUIDE.read_text()
    modules_by_claim: dict[str, set[str]] = {}
    for claim_id_cell, module_cell, _theorem_cell, _role in _extract_markdown_table_rows(
        theorem_guide_text, "## Open-Claim Lean Support Crosswalk"
    ):
        modules_by_claim.setdefault(claim_id_cell.strip("`"), set()).update(
            _normalize_theorem_guide_lean_targets(_extract_markdown_link_targets(module_cell))
        )
    return modules_by_claim


def _resolve_theorem_guide_lean_path(target: str) -> Path:
    repo_marker = "quadratic-residue-reptends/"
    relative = target.split(repo_marker, 1)[1] if repo_marker in target else target.lstrip("/")
    if relative.startswith("QRTour/"):
        relative = f"lean/{relative}"
    path = ROOT / relative
    assert path.suffix == ".lean", f"expected Lean module path, got: {target}"
    assert path.exists(), f"theorem-guide Lean module path does not exist in this checkout: {path}"
    return path


def _lean_declaration_names(path: Path) -> set[str]:
    pattern = re.compile(
        r"^(?:@\[[^\n]+\]\s*)?"
        r"(?:(?:private|noncomputable|protected|partial|unsafe)\s+)*"
        r"(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_'.]+)",
        re.MULTILINE,
    )
    return {match.group(1) for match in pattern.finditer(path.read_text())}


def _lean_name_resolves(name: str, declarations: set[str]) -> bool:
    return name in declarations or any(decl.endswith(f".{name}") for decl in declarations)


def _assert_certificate_lean_fixture_drift_gate() -> None:
    payload = certificate_lean_fixture_payload(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    theorem_guide_text = LEAN_GUIDE.read_text()

    assert payload["schema"] == "certificate-lean-fixtures-v1"
    assert payload["summary"]["emitted_fixture_count"] == 2
    for fixture in payload["fixtures"]:
        module_path = ROOT / fixture["module_path"]
        declarations = _lean_declaration_names(module_path)
        unresolved = [
            theorem_name
            for theorem_name in fixture["theorem_names"]
            if not _lean_name_resolves(theorem_name, declarations)
        ]
        assert not unresolved, (
            f"{fixture['certificate_id']} lists theorem names not found in "
            f"{fixture['module_path']}: {unresolved}"
        )
        missing_guide_mentions = [
            qualified_name
            for qualified_name in fixture["qualified_theorem_names"]
            if qualified_name not in theorem_guide_text
        ]
        assert not missing_guide_mentions, (
            f"{fixture['certificate_id']} fixture theorem names are missing "
            f"from lean/THEOREM_GUIDE.md: {missing_guide_mentions}"
        )

        stub = fixture["copyable_lean_stub"]
        assert stub["kind"] == "not_remainder_to_coefficient_functional_projection"
        assert stub["record_theorem_name"] in fixture["theorem_names"]
        assert stub["projection_accessor"] == "not_remainderToCoefficientFunctional"
        assert stub["recommended_theorem_name"] == (
            f"{fixture['certificate_id']}_not_remainderToCoefficientFunctional"
        )
        assert f"theorem {stub['recommended_theorem_name']} :" in stub["code"]
        assert stub["record_theorem_name"] in stub["code"]
        assert f".{stub['projection_accessor']}" in stub["code"]


def _assert_certificate_lean_stub_scaffold_lint_gate() -> None:
    payload = certificate_lean_stub_payload(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert payload["schema"] == "certificate-lean-stubs-v1"
    assert payload["summary"]["source_schema"] == "certificate-lean-fixtures-v1"
    assert payload["summary"]["emitted_stub_count"] == 2
    assert payload["summary"]["lint_failed"] == 0
    for stub in payload["stubs"]:
        assert stub["stub_scaffold_status"] == "copyable_projection_stub"
        assert stub["lint_status"] == "passed"
        assert stub["lint_errors"] == []
        assert stub["record_theorem_name"] == (
            "coordinate_stateAlignments_one_five_certifiedConflict_eight_one"
        )
        assert stub["projection_accessor"] == "not_remainderToCoefficientFunctional"
        assert f"theorem {stub['stub_theorem_name']} :" in stub["copyable_lean_code"]
        assert stub["record_theorem_name"] in stub["copyable_lean_code"]
        assert f".{stub['projection_accessor']}" in stub["copyable_lean_code"]


def _assert_certificate_fixture_mapping_lint_gate() -> None:
    source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=68,
        namespace="QRTour.Composite68",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(10,),
        n_blocks=8,
    )
    assert source_ready["schema"] == "certificate-fixture-mapping-lint-v1"
    assert source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert source_ready["summary"]["source_ready"] is True
    assert source_ready["summary"]["promotes_claims"] is False
    assert source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    staged = certificate_fixture_mapping_lint_payload(
        candidate_base=30,
        candidate_n=7,
        namespace="QRTour.FutureN7",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(30,),
        n_blocks=8,
    )
    assert staged["summary"]["mapping_lint_status"] == (
        "scaffold_ready_pending_lean_source"
    )
    assert staged["summary"]["source_ready"] is False
    assert staged["summary"]["scaffold_ready"] is True
    assert staged["candidate"]["certificate_tuple"][:2] == [30, 7]
    assert staged["proposed_mapping"]["source_checks"]["namespace_found"] is False
    assert staged["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ]
    assert staged["proposed_mapping"]["stub_lint_status"] == "passed"
    recipe = staged["proposed_mapping"]["source_pinning_recipe"]
    assert recipe["recipe_id"] == "source_pinning_recipe_v1"
    assert recipe["status_transition"] == [
        "scaffold_ready_pending_lean_source",
        "source_ready_existing_mapping",
    ]
    assert recipe["required_theorem_names"] == staged["proposed_mapping"][
        "required_theorem_names"
    ]
    assert recipe["record_theorem_name"] == (
        "coordinate_stateAlignments_zero_three_certifiedConflict_eight_two"
    )
    assert recipe["projection_accessor"] == "not_remainderToCoefficientFunctional"
    assert recipe["copyable_stub_theorem_name"] == (
        "base30_n7_m1_blocks8_L2_not_remainderToCoefficientFunctional"
    )
    assert recipe["copyable_stub_field"] == "proposed_mapping.copyable_lean_stub.code"
    assert any("source_ready_existing_mapping" in step for step in recipe["steps"])
    assert "No registry IDs" in recipe["promotion_boundary"]

    n7_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=30,
        candidate_n=7,
        candidate_m=1,
        namespace="QRTour.FutureBase30N7",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert n7_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert n7_source_ready["summary"]["source_ready"] is True
    assert n7_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert n7_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    n14_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=30,
        candidate_n=14,
        candidate_m=1,
        namespace="QRTour.FutureBase30N14",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert n14_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert n14_source_ready["summary"]["source_ready"] is True
    assert n14_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert n14_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    n28_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=30,
        candidate_n=28,
        candidate_m=1,
        namespace="QRTour.FutureBase30N28",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert n28_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert n28_source_ready["summary"]["source_ready"] is True
    assert n28_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert n28_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base12_n10_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=12,
        candidate_n=10,
        candidate_m=1,
        namespace="QRTour.FutureBase12N10",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base12_n10_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base12_n10_source_ready["summary"]["source_ready"] is True
    assert base12_n10_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base12_n10_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base10_n102_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=102,
        candidate_m=4,
        namespace="QRTour.FutureBase10N102",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base10_n102_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base10_n102_source_ready["summary"]["source_ready"] is True
    assert base10_n102_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base10_n102_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base7_n5_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=7,
        candidate_n=5,
        candidate_m=1,
        namespace="QRTour.FutureBase7N5",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base7_n5_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base7_n5_source_ready["summary"]["source_ready"] is True
    assert base7_n5_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base7_n5_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base12_n5_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=12,
        candidate_n=5,
        candidate_m=1,
        namespace="QRTour.FutureBase12N5",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base12_n5_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base12_n5_source_ready["summary"]["source_ready"] is True
    assert base12_n5_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base12_n5_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base30_n34_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=30,
        candidate_n=34,
        candidate_m=3,
        namespace="QRTour.FutureBase30N34",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base30_n34_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base30_n34_source_ready["summary"]["source_ready"] is True
    assert base30_n34_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base30_n34_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base7_n93_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=7,
        candidate_n=93,
        candidate_m=6,
        namespace="QRTour.FutureBase7N93",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base7_n93_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base7_n93_source_ready["summary"]["source_ready"] is True
    assert base7_n93_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base7_n93_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base10_n39_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=39,
        candidate_m=5,
        namespace="QRTour.FutureBase10N39",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base10_n39_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base10_n39_source_ready["summary"]["source_ready"] is True
    assert base10_n39_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base10_n39_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base10_n78_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=78,
        candidate_m=5,
        namespace="QRTour.FutureBase10N78",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base10_n78_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base10_n78_source_ready["summary"]["source_ready"] is True
    assert base10_n78_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base10_n78_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base10_n96_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=96,
        candidate_m=2,
        namespace="QRTour.FutureBase10N96",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base10_n96_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base10_n96_source_ready["summary"]["source_ready"] is True
    assert base10_n96_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base10_n96_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base12_n35_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=12,
        candidate_n=35,
        candidate_m=2,
        namespace="QRTour.FutureBase12N35",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base12_n35_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base12_n35_source_ready["summary"]["source_ready"] is True
    assert base12_n35_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base12_n35_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base12_n31_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=12,
        candidate_n=31,
        candidate_m=6,
        namespace="QRTour.FutureBase12N31",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base12_n31_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base12_n31_source_ready["summary"]["source_ready"] is True
    assert base12_n31_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base12_n31_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    auto = certificate_first_scaffold_mapping_lint_payload(
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert auto["summary"]["candidate_selection_mode"] == "first_scaffold_only"
    assert auto["summary"]["auto_selected_candidate"] is True
    assert auto["summary"]["namespace_auto_generated"] is True
    assert auto["summary"]["skipped_source_pinned_candidates"] == 2
    assert auto["candidate"]["certificate_tuple"] == [12, 70, 2, 144, 2, 4, 3, 2363392]
    assert auto["proposed_mapping"]["namespace"] == "QRTour.FutureBase12N70"
    assert auto["proposed_mapping"]["source_pinning_recipe"][
        "record_theorem_name"
    ] == "coordinate_stateAlignments_one_seven_certifiedConflict_eight_three"
    assert auto["proposed_mapping"]["source_pinning_recipe"][
        "copyable_stub_theorem_name"
    ] == "base12_n70_m2_blocks8_L3_not_remainderToCoefficientFunctional"
    package_plan = auto["proposed_mapping"]["lean_package_plan"]
    assert package_plan["plan_id"] == "lean_finite_package_plan_v1"
    assert package_plan["worth_proving_next"] is True
    assert package_plan["decision"] == "prove_next_finite_obstruction_example"
    assert package_plan["record_theorem_name"] == (
        "coordinate_stateAlignments_one_seven_certifiedConflict_eight_three"
    )
    assert package_plan["conflict_shape"]["conflict_remainder_state"] == 4
    assert package_plan["conflict_shape"]["conflict_positions"] == [1, 7]
    assert package_plan["conflict_shape"]["conflict_coefficients"] == [8, 32768]
    assert package_plan["conflict_shape"]["conflict_carry_states"] == [0, 936]
    assert package_plan["conflict_shape"]["conflict_block_values"] == [8, 8]
    assert package_plan["boundary_note"].startswith("finite example package only")


def test_certificate_lean_fixture_payload_source_pins_existing_lean_surface() -> None:
    _assert_certificate_lean_fixture_drift_gate()


def test_certificate_lean_stub_scaffold_lint_payload_stays_consistent() -> None:
    _assert_certificate_lean_stub_scaffold_lint_gate()


def test_certificate_fixture_mapping_lint_payload_stages_future_packages() -> None:
    _assert_certificate_fixture_mapping_lint_gate()


def test_registry_summary_blocks_match_registry_data() -> None:
    expected_summary = list(render_registry_summary_lines())
    expected_open = list(render_open_claim_lines())
    expected_proof_system_legend = list(render_proof_system_legend_lines())
    expected_readme_lean_claim_surface = list(render_readme_lean_claim_surface_lines())
    expected_throughline_thesis = list(render_throughline_research_thesis_lines())
    expected_throughline_ladder = list(render_throughline_witness_ladder_lines())
    expected_claim_table = list(render_claim_table_lines())
    expected_claim_carrier_table = list(render_lean_claim_carrier_lines())
    expected_open_claim_boundary_table = list(render_lean_open_claim_boundary_lines())
    expected_open_claim_support = list(render_open_claim_lean_support_lines())
    expected_throughline_layers = list(render_theorem_guide_throughline_layer_lines())
    expected_proof_status_footer = list(render_proof_status_footer_lines())
    expected_proof_track_five_notes = list(render_proof_status_track_five_notes_lines())
    expected_vocabulary_table = list(render_vocabulary_table_lines())
    expected_status_source = list(render_theorem_guide_status_source_lines())
    expected_module_index_source = list(render_theorem_guide_module_index_source_lines())
    expected_module_index = list(render_lean_module_index_lines())
    expected_worked_examples = list(render_lean_worked_example_lines())
    expected_examples_open_boundary_note = list(render_examples_open_boundary_note_lines())
    expected_next_frontier = list(render_theorem_guide_next_frontier_lines())
    expected_witness_summary = list(render_theorem_witness_summary_lines())
    expected_same_core_boundary_note = list(render_same_core_boundary_note_lines())
    expected_witness_table = list(render_theorem_witness_table_lines())
    expected_qr_tour_imports = list(render_qr_tour_import_lines())
    expected_geometric_stack_imports = list(render_geometric_stack_import_lines())

    readme_text = README.read_text()
    assert _extract_block(
        readme_text,
        "<!-- THROUGHLINE_RESEARCH_THESIS_START -->",
        "<!-- THROUGHLINE_RESEARCH_THESIS_END -->",
    ) == expected_throughline_thesis
    assert _extract_block(readme_text, "<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->") == expected_summary
    assert _extract_block(readme_text, "<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->") == expected_open
    assert _extract_block(readme_text, "<!-- PROOF_SYSTEM_LEGEND_START -->", "<!-- PROOF_SYSTEM_LEGEND_END -->") == expected_proof_system_legend
    assert _normalize_repo_link_targets(
        _extract_block(
            readme_text,
            "<!-- README_LEAN_CLAIM_SURFACE_START -->",
            "<!-- README_LEAN_CLAIM_SURFACE_END -->",
        )
    ) == _normalize_repo_link_targets(expected_readme_lean_claim_surface)

    atlas_text = (DOCS_DIR / "PROOF_STATUS_ATLAS.md").read_text()
    assert _extract_block(atlas_text, "<!-- PROOF_SYSTEM_LEGEND_START -->", "<!-- PROOF_SYSTEM_LEGEND_END -->") == expected_proof_system_legend
    assert _extract_block(atlas_text, "<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->") == expected_summary
    assert _extract_block(atlas_text, "<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->") == expected_open
    assert _normalize_repo_link_targets(
        _extract_block(atlas_text, "<!-- CLAIM_TABLE_START -->", "<!-- CLAIM_TABLE_END -->")
    ) == _normalize_repo_link_targets(expected_claim_table)
    assert _normalize_repo_link_targets(
        _extract_block(atlas_text, "<!-- PROOF_STATUS_FOOTER_START -->", "<!-- PROOF_STATUS_FOOTER_END -->")
    ) == _normalize_repo_link_targets(expected_proof_status_footer)
    assert _normalize_repo_link_targets(
        _extract_block(
            atlas_text,
            "<!-- PROOF_STATUS_TRACK_FIVE_NOTES_START -->",
            "<!-- PROOF_STATUS_TRACK_FIVE_NOTES_END -->",
        )
    ) == _normalize_repo_link_targets(expected_proof_track_five_notes)

    vocabulary_text = (DOCS_DIR / "VOCABULARY.md").read_text()
    assert _extract_block(vocabulary_text, "<!-- VOCABULARY_TABLE_START -->", "<!-- VOCABULARY_TABLE_END -->") == expected_vocabulary_table

    theorem_guide_text = LEAN_GUIDE.read_text()
    assert _normalize_repo_link_targets(
        _extract_block(
            theorem_guide_text,
            "<!-- THEOREM_GUIDE_STATUS_SOURCE_START -->",
            "<!-- THEOREM_GUIDE_STATUS_SOURCE_END -->",
        )
    ) == _normalize_repo_link_targets(expected_status_source)
    assert _normalize_repo_link_targets(
        _extract_block(
            theorem_guide_text,
            "<!-- THEOREM_GUIDE_THROUGHLINE_LAYERS_START -->",
            "<!-- THEOREM_GUIDE_THROUGHLINE_LAYERS_END -->",
        )
    ) == _normalize_repo_link_targets(expected_throughline_layers)
    assert _extract_block(theorem_guide_text, "<!-- PROOF_SYSTEM_LEGEND_START -->", "<!-- PROOF_SYSTEM_LEGEND_END -->") == expected_proof_system_legend
    assert _normalize_repo_link_targets(
        _extract_block(
            theorem_guide_text,
            "<!-- THEOREM_GUIDE_CLAIM_CARRIERS_START -->",
            "<!-- THEOREM_GUIDE_CLAIM_CARRIERS_END -->",
        )
    ) == _normalize_repo_link_targets(expected_claim_carrier_table)
    assert _normalize_repo_link_targets(
        _extract_block(
            theorem_guide_text,
            "<!-- THEOREM_GUIDE_OPEN_BOUNDARY_START -->",
            "<!-- THEOREM_GUIDE_OPEN_BOUNDARY_END -->",
        )
    ) == _normalize_repo_link_targets(expected_open_claim_boundary_table)
    assert _normalize_repo_link_targets(
        _extract_block(
            theorem_guide_text,
            "<!-- THEOREM_GUIDE_WORKED_EXAMPLES_START -->",
            "<!-- THEOREM_GUIDE_WORKED_EXAMPLES_END -->",
        )
    ) == _normalize_repo_link_targets(expected_worked_examples)
    assert _normalize_repo_link_targets(
        _extract_block(
            theorem_guide_text,
            "<!-- OPEN_CLAIM_LEAN_SUPPORT_START -->",
            "<!-- OPEN_CLAIM_LEAN_SUPPORT_END -->",
        )
    ) == _normalize_repo_link_targets(expected_open_claim_support)
    assert _normalize_repo_link_targets(
        _extract_block(
            theorem_guide_text,
            "<!-- THEOREM_GUIDE_MODULE_INDEX_SOURCE_START -->",
            "<!-- THEOREM_GUIDE_MODULE_INDEX_SOURCE_END -->",
        )
    ) == _normalize_repo_link_targets(expected_module_index_source)
    assert _normalize_repo_link_targets(
        _extract_block(theorem_guide_text, "<!-- LEAN_MODULE_INDEX_START -->", "<!-- LEAN_MODULE_INDEX_END -->")
    ) == _normalize_repo_link_targets(expected_module_index)
    assert _normalize_repo_link_targets(
        _extract_block(
            theorem_guide_text,
            "<!-- THEOREM_GUIDE_NEXT_FRONTIER_START -->",
            "<!-- THEOREM_GUIDE_NEXT_FRONTIER_END -->",
        )
    ) == _normalize_repo_link_targets(expected_next_frontier)

    examples_text = EXAMPLES_SURFACE.read_text()
    assert _normalize_repo_link_targets(
        _extract_block(
            examples_text,
            "<!-- EXAMPLES_WORKED_EXAMPLE_INDEX_START -->",
            "<!-- EXAMPLES_WORKED_EXAMPLE_INDEX_END -->",
        )
    ) == _normalize_repo_link_targets(expected_worked_examples)
    assert _normalize_repo_link_targets(
        _extract_block(
            examples_text,
            "<!-- EXAMPLES_OPEN_BOUNDARY_NOTE_START -->",
            "<!-- EXAMPLES_OPEN_BOUNDARY_NOTE_END -->",
        )
    ) == _normalize_repo_link_targets(expected_examples_open_boundary_note)

    qrt_surface_text = QRT_SURFACE.read_text()
    assert _extract_block(
        qrt_surface_text,
        "-- QRT_SURFACE_IMPORTS_START",
        "-- QRT_SURFACE_IMPORTS_END",
    ) == expected_qr_tour_imports

    geometric_stack_text = GEOMETRIC_STACK_SURFACE.read_text()
    assert _extract_block(
        geometric_stack_text,
        "-- GEOMETRIC_STACK_IMPORTS_START",
        "-- GEOMETRIC_STACK_IMPORTS_END",
    ) == expected_geometric_stack_imports

    witness_text = WITNESS_ATLAS.read_text()
    assert _extract_block(witness_text, "<!-- PROOF_SYSTEM_LEGEND_START -->", "<!-- PROOF_SYSTEM_LEGEND_END -->") == expected_proof_system_legend
    assert _extract_block(
        witness_text,
        "<!-- THROUGHLINE_RESEARCH_THESIS_START -->",
        "<!-- THROUGHLINE_RESEARCH_THESIS_END -->",
    ) == expected_throughline_thesis
    assert _extract_block(witness_text, "<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->") == expected_summary
    assert _extract_block(witness_text, "<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->") == expected_open
    assert _normalize_repo_link_targets(
        _extract_block(
            witness_text,
            "<!-- THROUGHLINE_WITNESS_LADDER_START -->",
            "<!-- THROUGHLINE_WITNESS_LADDER_END -->",
        )
    ) == _normalize_repo_link_targets(expected_throughline_ladder)
    assert _extract_block(witness_text, "<!-- THEOREM_WITNESS_SUMMARY_START -->", "<!-- THEOREM_WITNESS_SUMMARY_END -->") == expected_witness_summary
    assert _normalize_repo_link_targets(
        _extract_block(witness_text, "<!-- SAME_CORE_BOUNDARY_NOTE_START -->", "<!-- SAME_CORE_BOUNDARY_NOTE_END -->")
    ) == _normalize_repo_link_targets(expected_same_core_boundary_note)
    assert _normalize_repo_link_targets(
        _extract_block(witness_text, "<!-- THEOREM_WITNESS_TABLE_START -->", "<!-- THEOREM_WITNESS_TABLE_END -->")
    ) == _normalize_repo_link_targets(expected_witness_table)


def test_theorem_guide_claim_tables_cover_the_lean_backed_claim_boundary() -> None:
    records = load_claim_registry()
    claim_status = {record.id: record.status for record in records}
    module_claim_ids = {
        claim_id
        for module in load_lean_module_index()
        for claim_id in module.claim_ids
    }
    expected_atlas_backed = {
        claim_id for claim_id in module_claim_ids if claim_status[claim_id] != "open"
    }
    expected_open_boundary = {
        claim_id for claim_id in module_claim_ids if claim_status[claim_id] == "open"
    }

    theorem_guide_text = LEAN_GUIDE.read_text()
    assert _extract_table_claim_ids(theorem_guide_text, "## Atlas-Backed Claim Carriers") == expected_atlas_backed
    assert _extract_table_claim_ids(theorem_guide_text, "## Open Claims With Lean Boundary Work") == expected_open_boundary


def test_readme_lean_claim_surface_covers_non_open_claim_carriers() -> None:
    expected_claim_ids = [record.claim_id for record in load_lean_claim_carriers()]
    claim_surface_lines = _extract_block(
        README.read_text(),
        "<!-- README_LEAN_CLAIM_SURFACE_START -->",
        "<!-- README_LEAN_CLAIM_SURFACE_END -->",
    )
    claim_ids = [
        claim_id
        for line in claim_surface_lines
        for claim_id in re.findall(r"`([^`]+)`", line)
        if not claim_id.startswith("QRTour.")
    ]

    assert claim_ids == expected_claim_ids


def test_theorem_guide_theorem_names_resolve_in_listed_lean_modules() -> None:
    theorem_guide_text = LEAN_GUIDE.read_text()
    witnesses = theorem_witnesses_by_claim()
    for row in _extract_markdown_table_rows(theorem_guide_text, "## Atlas-Backed Claim Carriers"):
        claim_id_cell, _status, module_cell, theorem_cell, witness_cell = row
        claim_id = claim_id_cell.strip("`")
        module_paths = [_resolve_theorem_guide_lean_path(target) for target in _extract_markdown_link_targets(module_cell)]
        declarations = set().union(*(_lean_declaration_names(path) for path in module_paths))
        theorem_names = [name.strip().strip("`") for name in theorem_cell.split(",")]
        unresolved = [name for name in theorem_names if not _lean_name_resolves(name, declarations)]
        assert not unresolved, (
            f"{claim_id} lists theorem names not found in the referenced Lean modules: {unresolved}"
        )
        expected_witness_ids = [
            witness.id for witness in witnesses[claim_id] if witness.kind == "theorem-witness"
        ]
        assert _extract_code_ids(witness_cell) == expected_witness_ids


def test_theorem_guide_worked_example_hook_points_to_existing_witnesses() -> None:
    theorem_guide_text = LEAN_GUIDE.read_text()
    witness_atlas_text = WITNESS_ATLAS.read_text()
    section = theorem_guide_text.split("## Worked Example Entry Points", 1)[1].split(
        "## Open Claims With Lean Boundary Work", 1
    )[0]

    assert "[THEOREM_WITNESS_ATLAS.md]" in section

    rows = _extract_markdown_table_rows(theorem_guide_text, "## Worked Example Entry Points")
    expected_rows = {
        record.namespace: (list(record.claim_ids), list(record.theorem_names), list(record.witness_ids))
        for record in load_lean_worked_examples()
    }
    assert len(rows) == len(expected_rows)

    for namespace, claim_cell, theorem_cell, _role, witness_cell in rows:
        assert "[QRTour/Examples.lean]" in namespace
        module_path = _resolve_theorem_guide_lean_path(_extract_markdown_link_targets(namespace)[0])
        declarations = _lean_declaration_names(module_path)
        claim_ids = _extract_code_ids(claim_cell)
        code_ids = _extract_code_ids(witness_cell)
        matching_namespaces = [name for name in expected_rows if f"`{name}`" in namespace]
        assert len(matching_namespaces) == 1, f"unexpected theorem-guide example namespace row: {namespace}"
        expected_claim_ids, expected_theorem_names, expected_witness_ids = expected_rows[matching_namespaces[0]]
        theorem_names = [name.strip().strip("`") for name in theorem_cell.split(",")]
        assert claim_ids == expected_claim_ids
        assert theorem_names == expected_theorem_names
        unresolved = [name for name in theorem_names if not _lean_name_resolves(name, declarations)]
        assert not unresolved, (
            f"worked-example row {matching_namespaces[0]} lists theorem names not found in "
            f"{module_path}: {unresolved}"
        )
        assert code_ids == expected_witness_ids
        for witness_id in code_ids:
            assert f"`{witness_id}`" in witness_atlas_text, (
                f"theorem-guide worked-example hook references missing witness atlas id {witness_id}"
            )


def test_theorem_guide_open_claim_support_theorem_names_resolve() -> None:
    theorem_guide_text = LEAN_GUIDE.read_text()
    for row in _extract_markdown_table_rows(theorem_guide_text, "## Open-Claim Lean Support Crosswalk"):
        claim_id, module_cell, theorem_cell, _role = row
        module_targets = _extract_markdown_link_targets(module_cell)
        assert module_targets, f"{claim_id} should reference a Lean module in the support crosswalk"
        module_path = _resolve_theorem_guide_lean_path(module_targets[0])
        declarations = _lean_declaration_names(module_path)
        theorem_names = [name.strip().strip("`") for name in theorem_cell.split(",")]
        unresolved = [name for name in theorem_names if not _lean_name_resolves(name, declarations)]
        assert not unresolved, (
            f"{claim_id} lists open-boundary theorem names not found in {module_path}: {unresolved}"
        )


def test_theorem_guide_open_claim_boundary_modules_resolve() -> None:
    theorem_guide_text = LEAN_GUIDE.read_text()
    for row in _extract_markdown_table_rows(theorem_guide_text, "## Open Claims With Lean Boundary Work"):
        claim_id, boundary_cell = row
        module_targets = _extract_markdown_link_targets(boundary_cell)
        assert module_targets, f"{claim_id} should reference at least one Lean module in its boundary row"
        for target in module_targets:
            _resolve_theorem_guide_lean_path(target)


def test_theorem_guide_open_claim_boundary_rows_match_registry_segments() -> None:
    theorem_guide_text = LEAN_GUIDE.read_text()
    boundary_rows = {
        claim_id_cell.strip("`"): boundary_cell
        for claim_id_cell, boundary_cell in _extract_markdown_table_rows(
            theorem_guide_text, "## Open Claims With Lean Boundary Work"
        )
    }

    for record in load_lean_open_claim_boundaries():
        assert record.claim_id in boundary_rows, (
            f"missing theorem-guide open-boundary row for {record.claim_id}"
        )
        rendered_segments = boundary_rows[record.claim_id].split("; ")
        assert len(rendered_segments) == len(record.segments), (
            f"{record.claim_id} should render exactly one theorem-guide segment per "
            "lean_open_claim_boundaries.json segment"
        )
        for rendered_segment, expected_segment in zip(rendered_segments, record.segments, strict=True):
            assert rendered_segment.endswith(expected_segment.summary), (
                f"{record.claim_id} theorem-guide segment lost or changed summary text from "
                "lean_open_claim_boundaries.json"
            )
            rendered_targets = _normalize_theorem_guide_lean_targets(
                _extract_markdown_link_targets(rendered_segment)
            )
            assert rendered_targets == list(expected_segment.module_paths), (
                f"{record.claim_id} theorem-guide segment module coverage drifted from "
                "lean_open_claim_boundaries.json"
            )


def test_theorem_guide_open_claim_boundary_and_support_modules_stay_aligned() -> None:
    boundary_modules_by_claim = _theorem_guide_open_claim_boundary_modules_by_claim()
    support_modules_by_claim = _theorem_guide_open_claim_support_modules_by_claim()

    assert boundary_modules_by_claim == support_modules_by_claim, (
        "theorem-guide open-boundary rows and support crosswalk should cover the same Lean "
        "modules for each open claim"
    )


def test_normalized_source_and_vocabulary_ids_are_visible_in_docs() -> None:
    literature_map = (DOCS_DIR / "LITERATURE_MAP.md").read_text()
    vocabulary = (DOCS_DIR / "VOCABULARY.md").read_text()

    for source_id in [
        "conrad_orders",
        "conrad_qr_patterns",
        "conrad_crt",
        "conrad_qp",
        "leavitt_repeating_decimals",
        "allouche_shallit",
    ]:
        assert f"`{source_id}`" in literature_map

    for vocabulary_id in [
        "remainder_k",
        "quotient_q",
        "skeleton",
        "carry_layer",
        "preimage_fiber_profile",
        "visible_preimage_compression",
        "hidden_graph_obstruction",
        "body_term",
        "correction_term",
        "good_mode",
        "qr_generator",
        "remainder_orbit",
    ]:
        assert f"`{vocabulary_id}`" in vocabulary
