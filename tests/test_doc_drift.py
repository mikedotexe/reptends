import re
from pathlib import Path

from bridge_reptends import (
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
    assert "Instrument Atlas" in carry_doc
    assert "search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20" in carry_doc

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
