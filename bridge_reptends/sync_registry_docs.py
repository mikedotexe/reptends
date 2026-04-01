"""
Sync registry-backed Markdown blocks into public docs.

This keeps selected outward surfaces derived from the machine-readable claim,
Lean-module, theorem-witness, and vocabulary registries rather than maintained
by hand.
"""

from __future__ import annotations

from collections.abc import Iterable
from pathlib import Path

from .registry import (
    render_claim_table_lines,
    render_lean_module_index_lines,
    render_open_claim_lean_support_lines,
    render_open_claim_lines,
    render_proof_status_footer_lines,
    render_proof_status_track_five_notes_lines,
    render_proof_system_legend_lines,
    render_registry_summary_lines,
    render_same_core_boundary_note_lines,
    render_theorem_guide_claim_carrier_lines,
    render_theorem_guide_module_index_source_lines,
    render_theorem_guide_next_frontier_lines,
    render_theorem_guide_open_boundary_lines,
    render_theorem_guide_status_source_lines,
    render_theorem_witness_summary_lines,
    render_theorem_witness_table_lines,
    render_vocabulary_table_lines,
)


ROOT = Path(__file__).resolve().parent.parent


def _replace_block(text: str, start_marker: str, end_marker: str, lines: Iterable[str]) -> str:
    start = text.index(start_marker) + len(start_marker)
    end = text.index(end_marker)
    body = "\n" + "\n".join(lines) + "\n"
    return text[:start] + body + text[end:]


def sync_registry_docs() -> tuple[Path, ...]:
    """Rewrite the registry-backed blocks in the main Markdown docs."""
    updates = {
        ROOT / "README.md": (
            ("<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->", render_registry_summary_lines()),
            ("<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->", render_open_claim_lines()),
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
        ),
        ROOT / "docs" / "PROOF_STATUS_ATLAS.md": (
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
            ("<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->", render_registry_summary_lines()),
            ("<!-- CLAIM_TABLE_START -->", "<!-- CLAIM_TABLE_END -->", render_claim_table_lines()),
            ("<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->", render_open_claim_lines()),
            ("<!-- PROOF_STATUS_FOOTER_START -->", "<!-- PROOF_STATUS_FOOTER_END -->", render_proof_status_footer_lines()),
            (
                "<!-- PROOF_STATUS_TRACK_FIVE_NOTES_START -->",
                "<!-- PROOF_STATUS_TRACK_FIVE_NOTES_END -->",
                render_proof_status_track_five_notes_lines(),
            ),
        ),
        ROOT / "docs" / "VOCABULARY.md": (
            ("<!-- VOCABULARY_TABLE_START -->", "<!-- VOCABULARY_TABLE_END -->", render_vocabulary_table_lines()),
        ),
        ROOT / "lean" / "THEOREM_GUIDE.md": (
            (
                "<!-- THEOREM_GUIDE_STATUS_SOURCE_START -->",
                "<!-- THEOREM_GUIDE_STATUS_SOURCE_END -->",
                render_theorem_guide_status_source_lines(),
            ),
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
            (
                "<!-- THEOREM_GUIDE_CLAIM_CARRIERS_START -->",
                "<!-- THEOREM_GUIDE_CLAIM_CARRIERS_END -->",
                render_theorem_guide_claim_carrier_lines(),
            ),
            (
                "<!-- THEOREM_GUIDE_OPEN_BOUNDARY_START -->",
                "<!-- THEOREM_GUIDE_OPEN_BOUNDARY_END -->",
                render_theorem_guide_open_boundary_lines(),
            ),
            (
                "<!-- OPEN_CLAIM_LEAN_SUPPORT_START -->",
                "<!-- OPEN_CLAIM_LEAN_SUPPORT_END -->",
                render_open_claim_lean_support_lines(),
            ),
            (
                "<!-- THEOREM_GUIDE_MODULE_INDEX_SOURCE_START -->",
                "<!-- THEOREM_GUIDE_MODULE_INDEX_SOURCE_END -->",
                render_theorem_guide_module_index_source_lines(),
            ),
            ("<!-- LEAN_MODULE_INDEX_START -->", "<!-- LEAN_MODULE_INDEX_END -->", render_lean_module_index_lines()),
            (
                "<!-- THEOREM_GUIDE_NEXT_FRONTIER_START -->",
                "<!-- THEOREM_GUIDE_NEXT_FRONTIER_END -->",
                render_theorem_guide_next_frontier_lines(),
            ),
        ),
        ROOT / "docs" / "THEOREM_WITNESS_ATLAS.md": (
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
            ("<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->", render_registry_summary_lines()),
            ("<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->", render_open_claim_lines()),
            ("<!-- THEOREM_WITNESS_SUMMARY_START -->", "<!-- THEOREM_WITNESS_SUMMARY_END -->", render_theorem_witness_summary_lines()),
            ("<!-- SAME_CORE_BOUNDARY_NOTE_START -->", "<!-- SAME_CORE_BOUNDARY_NOTE_END -->", render_same_core_boundary_note_lines()),
            ("<!-- THEOREM_WITNESS_TABLE_START -->", "<!-- THEOREM_WITNESS_TABLE_END -->", render_theorem_witness_table_lines()),
        ),
    }

    touched: list[Path] = []
    for path, replacements in updates.items():
        text = path.read_text()
        updated = text
        for start_marker, end_marker, lines in replacements:
            updated = _replace_block(updated, start_marker, end_marker, lines)
        if updated != text:
            path.write_text(updated)
            touched.append(path)
    return tuple(touched)


def main() -> None:
    touched = sync_registry_docs()
    if touched:
        for path in touched:
            print(path.relative_to(ROOT))
    else:
        print("registry-backed docs already synchronized")


if __name__ == "__main__":
    main()
