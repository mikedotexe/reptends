from pathlib import Path

from bridge_reptends import (
    render_claim_table_lines,
    render_lean_module_index_lines,
    render_open_claim_lines,
    render_registry_summary_lines,
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


def _extract_block(text: str, start_marker: str, end_marker: str) -> list[str]:
    start = text.index(start_marker) + len(start_marker)
    end = text.index(end_marker)
    return [line.rstrip() for line in text[start:end].strip().splitlines()]


def test_registry_summary_blocks_match_registry_data() -> None:
    expected_summary = list(render_registry_summary_lines())
    expected_open = list(render_open_claim_lines())
    expected_claim_table = list(render_claim_table_lines())
    expected_vocabulary_table = list(render_vocabulary_table_lines())
    expected_module_index = list(render_lean_module_index_lines())
    expected_witness_summary = list(render_theorem_witness_summary_lines())
    expected_witness_table = list(render_theorem_witness_table_lines())

    for path in [README, DOCS_DIR / "PROOF_STATUS_ATLAS.md"]:
        text = path.read_text()
        assert _extract_block(text, "<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->") == expected_summary
        assert _extract_block(text, "<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->") == expected_open

    atlas_text = (DOCS_DIR / "PROOF_STATUS_ATLAS.md").read_text()
    assert _extract_block(atlas_text, "<!-- CLAIM_TABLE_START -->", "<!-- CLAIM_TABLE_END -->") == expected_claim_table

    vocabulary_text = (DOCS_DIR / "VOCABULARY.md").read_text()
    assert _extract_block(vocabulary_text, "<!-- VOCABULARY_TABLE_START -->", "<!-- VOCABULARY_TABLE_END -->") == expected_vocabulary_table

    theorem_guide_text = LEAN_GUIDE.read_text()
    assert _extract_block(theorem_guide_text, "<!-- LEAN_MODULE_INDEX_START -->", "<!-- LEAN_MODULE_INDEX_END -->") == expected_module_index

    witness_text = WITNESS_ATLAS.read_text()
    assert _extract_block(witness_text, "<!-- THEOREM_WITNESS_SUMMARY_START -->", "<!-- THEOREM_WITNESS_SUMMARY_END -->") == expected_witness_summary
    assert _extract_block(witness_text, "<!-- THEOREM_WITNESS_TABLE_START -->", "<!-- THEOREM_WITNESS_TABLE_END -->") == expected_witness_table


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
