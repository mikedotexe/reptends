import re
from pathlib import Path

from bridge_reptends import (
    load_claim_registry,
    load_lean_module_index,
    render_claim_table_lines,
    render_lean_claim_carrier_lines,
    render_lean_open_claim_boundary_lines,
    render_lean_module_index_lines,
    render_open_claim_lines,
    render_open_claim_lean_support_lines,
    render_proof_status_footer_lines,
    render_proof_status_track_five_notes_lines,
    render_proof_system_legend_lines,
    render_registry_summary_lines,
    render_same_core_boundary_note_lines,
    render_theorem_guide_module_index_source_lines,
    render_theorem_guide_next_frontier_lines,
    render_theorem_guide_status_source_lines,
    render_theorem_witness_summary_lines,
    render_theorem_witness_table_lines,
    render_vocabulary_table_lines,
)


ROOT = Path(__file__).resolve().parent.parent

README = ROOT / "README.md"
AGENTS = ROOT / "AGENTS.md"
CLAUDE = ROOT / "CLAUDE.md"
DISCOVERIES = ROOT / "DISCOVERIES.md"
DOCS_DIR = ROOT / "docs"
LEAN_GUIDE = ROOT / "lean" / "THEOREM_GUIDE.md"
WITNESS_ATLAS = DOCS_DIR / "THEOREM_WITNESS_ATLAS.md"
AGDA_CORRESPONDENCE = DOCS_DIR / "AGDA_CORRESPONDENCE.md"
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
    expected_claim_table = list(render_claim_table_lines())
    expected_claim_carrier_table = list(render_lean_claim_carrier_lines())
    expected_open_claim_boundary_table = list(render_lean_open_claim_boundary_lines())
    expected_open_claim_support = list(render_open_claim_lean_support_lines())
    expected_proof_status_footer = list(render_proof_status_footer_lines())
    expected_proof_track_five_notes = list(render_proof_status_track_five_notes_lines())
    expected_vocabulary_table = list(render_vocabulary_table_lines())
    expected_status_source = list(render_theorem_guide_status_source_lines())
    expected_module_index_source = list(render_theorem_guide_module_index_source_lines())
    expected_module_index = list(render_lean_module_index_lines())
    expected_next_frontier = list(render_theorem_guide_next_frontier_lines())
    expected_witness_summary = list(render_theorem_witness_summary_lines())
    expected_same_core_boundary_note = list(render_same_core_boundary_note_lines())
    expected_witness_table = list(render_theorem_witness_table_lines())

    readme_text = README.read_text()
    assert _extract_block(readme_text, "<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->") == expected_summary
    assert _extract_block(readme_text, "<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->") == expected_open
    assert _extract_block(readme_text, "<!-- PROOF_SYSTEM_LEGEND_START -->", "<!-- PROOF_SYSTEM_LEGEND_END -->") == expected_proof_system_legend

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

    witness_text = WITNESS_ATLAS.read_text()
    assert _extract_block(witness_text, "<!-- PROOF_SYSTEM_LEGEND_START -->", "<!-- PROOF_SYSTEM_LEGEND_END -->") == expected_proof_system_legend
    assert _extract_block(witness_text, "<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->") == expected_summary
    assert _extract_block(witness_text, "<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->") == expected_open
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


def test_theorem_guide_theorem_names_resolve_in_listed_lean_modules() -> None:
    theorem_guide_text = LEAN_GUIDE.read_text()
    for row in _extract_markdown_table_rows(theorem_guide_text, "## Atlas-Backed Claim Carriers"):
        claim_id, _status, module_cell, theorem_cell = row
        module_paths = [_resolve_theorem_guide_lean_path(target) for target in _extract_markdown_link_targets(module_cell)]
        declarations = set().union(*(_lean_declaration_names(path) for path in module_paths))
        theorem_names = [name.strip().strip("`") for name in theorem_cell.split(",")]
        unresolved = [name for name in theorem_names if not _lean_name_resolves(name, declarations)]
        assert not unresolved, (
            f"{claim_id} lists theorem names not found in the referenced Lean modules: {unresolved}"
        )


def test_theorem_guide_open_claim_boundary_modules_resolve() -> None:
    theorem_guide_text = LEAN_GUIDE.read_text()
    for row in _extract_markdown_table_rows(theorem_guide_text, "## Open Claims With Lean Boundary Work"):
        claim_id, boundary_cell = row
        module_targets = _extract_markdown_link_targets(boundary_cell)
        assert module_targets, f"{claim_id} should reference at least one Lean module in its boundary row"
        for target in module_targets:
            _resolve_theorem_guide_lean_path(target)


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
        "body_term",
        "correction_term",
        "good_mode",
        "qr_generator",
        "remainder_orbit",
    ]:
        assert f"`{vocabulary_id}`" in vocabulary
