"""
Sync registry-backed Markdown blocks into public docs.

This keeps selected outward surfaces derived from the machine-readable claim,
Lean-module, theorem-witness, and vocabulary registries rather than maintained
by hand.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable
from pathlib import Path

from .registry import (
    render_claim_table_lines,
    render_carried_prefix_visibility_status_anchor_lines,
    render_carry_transducer_status_anchor_lines,
    render_examples_open_boundary_note_lines,
    render_geometric_stack_import_lines,
    render_geometric_stack_module_lines,
    render_lean_module_index_lines,
    render_lean_worked_example_lines,
    render_open_claim_lean_support_lines,
    render_open_claim_lines,
    render_proof_status_footer_lines,
    render_proof_status_track_five_notes_lines,
    render_proof_system_legend_lines,
    render_readme_lean_claim_surface_lines,
    render_registry_summary_lines,
    render_same_core_boundary_note_lines,
    render_theorem_guide_throughline_layer_lines,
    render_theorem_guide_claim_carrier_lines,
    render_theorem_guide_module_index_source_lines,
    render_theorem_guide_next_frontier_lines,
    render_theorem_guide_open_boundary_lines,
    render_theorem_guide_status_source_lines,
    render_theorem_witness_summary_lines,
    render_theorem_witness_table_lines,
    render_throughline_research_thesis_lines,
    render_throughline_witness_ladder_lines,
    render_vocabulary_table_lines,
    render_qr_tour_import_lines,
    render_qr_tour_module_lines,
    render_qr_tour_open_boundary_lines,
    render_qr_tour_theorem_surface_lines,
)


ROOT = Path(__file__).resolve().parent.parent


def _replace_block(text: str, start_marker: str, end_marker: str, lines: Iterable[str]) -> str:
    start = text.index(start_marker) + len(start_marker)
    end = text.index(end_marker)
    body = "\n" + "\n".join(lines) + "\n"
    return text[:start] + body + text[end:]


def registry_doc_updates() -> dict[Path, tuple[tuple[str, str, Iterable[str]], ...]]:
    """Return the current registry-backed Markdown replacement plan."""
    return {
        ROOT / "README.md": (
            (
                "<!-- THROUGHLINE_RESEARCH_THESIS_START -->",
                "<!-- THROUGHLINE_RESEARCH_THESIS_END -->",
                render_throughline_research_thesis_lines(),
            ),
            ("<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->", render_registry_summary_lines()),
            ("<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->", render_open_claim_lines()),
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
            (
                "<!-- README_LEAN_CLAIM_SURFACE_START -->",
                "<!-- README_LEAN_CLAIM_SURFACE_END -->",
                render_readme_lean_claim_surface_lines(),
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
        ROOT / "docs" / "AGDA_CORRESPONDENCE.md": (
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
        ),
        ROOT / "docs" / "VOCABULARY.md": (
            ("<!-- VOCABULARY_TABLE_START -->", "<!-- VOCABULARY_TABLE_END -->", render_vocabulary_table_lines()),
        ),
        ROOT / "docs" / "CARRY_TRANSDUCER.md": (
            (
                "<!-- CARRY_TRANSDUCER_STATUS_ANCHOR_START -->",
                "<!-- CARRY_TRANSDUCER_STATUS_ANCHOR_END -->",
                render_carry_transducer_status_anchor_lines(),
            ),
            (
                "<!-- CARRY_TRANSDUCER_THROUGHLINE_START -->",
                "<!-- CARRY_TRANSDUCER_THROUGHLINE_END -->",
                render_throughline_witness_ladder_lines(),
            ),
        ),
        ROOT / "docs" / "CARRIED_PREFIX_VISIBILITY.md": (
            (
                "<!-- CARRIED_PREFIX_VISIBILITY_STATUS_ANCHOR_START -->",
                "<!-- CARRIED_PREFIX_VISIBILITY_STATUS_ANCHOR_END -->",
                render_carried_prefix_visibility_status_anchor_lines(),
            ),
        ),
        ROOT / "lean" / "THEOREM_GUIDE.md": (
            (
                "<!-- THEOREM_GUIDE_STATUS_SOURCE_START -->",
                "<!-- THEOREM_GUIDE_STATUS_SOURCE_END -->",
                render_theorem_guide_status_source_lines(),
            ),
            (
                "<!-- THEOREM_GUIDE_THROUGHLINE_LAYERS_START -->",
                "<!-- THEOREM_GUIDE_THROUGHLINE_LAYERS_END -->",
                render_theorem_guide_throughline_layer_lines(),
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
                "<!-- THEOREM_GUIDE_WORKED_EXAMPLES_START -->",
                "<!-- THEOREM_GUIDE_WORKED_EXAMPLES_END -->",
                render_lean_worked_example_lines(),
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
        ROOT / "lean" / "QRTour.lean": (
            (
                "-- QRT_SURFACE_IMPORTS_START",
                "-- QRT_SURFACE_IMPORTS_END",
                render_qr_tour_import_lines(),
            ),
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
            (
                "<!-- QRT_SURFACE_THEOREM_SURFACE_START -->",
                "<!-- QRT_SURFACE_THEOREM_SURFACE_END -->",
                render_qr_tour_theorem_surface_lines(),
            ),
            (
                "<!-- QRT_SURFACE_OPEN_BOUNDARY_START -->",
                "<!-- QRT_SURFACE_OPEN_BOUNDARY_END -->",
                render_qr_tour_open_boundary_lines(),
            ),
            (
                "<!-- QRT_SURFACE_MODULES_START -->",
                "<!-- QRT_SURFACE_MODULES_END -->",
                render_qr_tour_module_lines(),
            ),
        ),
        ROOT / "lean" / "GeometricStack.lean": (
            (
                "-- GEOMETRIC_STACK_IMPORTS_START",
                "-- GEOMETRIC_STACK_IMPORTS_END",
                render_geometric_stack_import_lines(),
            ),
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
            (
                "<!-- GEOMETRIC_STACK_MODULES_START -->",
                "<!-- GEOMETRIC_STACK_MODULES_END -->",
                render_geometric_stack_module_lines(),
            ),
        ),
        ROOT / "lean" / "QRTour" / "Examples.lean": (
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
            (
                "<!-- EXAMPLES_WORKED_EXAMPLE_INDEX_START -->",
                "<!-- EXAMPLES_WORKED_EXAMPLE_INDEX_END -->",
                render_lean_worked_example_lines(),
            ),
            (
                "<!-- EXAMPLES_OPEN_BOUNDARY_NOTE_START -->",
                "<!-- EXAMPLES_OPEN_BOUNDARY_NOTE_END -->",
                render_examples_open_boundary_note_lines(),
            ),
        ),
        ROOT / "docs" / "THEOREM_WITNESS_ATLAS.md": (
            (
                "<!-- PROOF_SYSTEM_LEGEND_START -->",
                "<!-- PROOF_SYSTEM_LEGEND_END -->",
                render_proof_system_legend_lines(),
            ),
            (
                "<!-- THROUGHLINE_RESEARCH_THESIS_START -->",
                "<!-- THROUGHLINE_RESEARCH_THESIS_END -->",
                render_throughline_research_thesis_lines(),
            ),
            ("<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->", render_registry_summary_lines()),
            ("<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->", render_open_claim_lines()),
            (
                "<!-- THROUGHLINE_WITNESS_LADDER_START -->",
                "<!-- THROUGHLINE_WITNESS_LADDER_END -->",
                render_throughline_witness_ladder_lines(),
            ),
            ("<!-- THEOREM_WITNESS_SUMMARY_START -->", "<!-- THEOREM_WITNESS_SUMMARY_END -->", render_theorem_witness_summary_lines()),
            ("<!-- SAME_CORE_BOUNDARY_NOTE_START -->", "<!-- SAME_CORE_BOUNDARY_NOTE_END -->", render_same_core_boundary_note_lines()),
            ("<!-- THEOREM_WITNESS_TABLE_START -->", "<!-- THEOREM_WITNESS_TABLE_END -->", render_theorem_witness_table_lines()),
        ),
    }


def sync_registry_docs(*, check: bool = False) -> tuple[Path, ...]:
    """Rewrite or check the registry-backed blocks in the main Markdown docs."""
    touched: list[Path] = []
    for path, replacements in registry_doc_updates().items():
        text = path.read_text()
        updated = text
        for start_marker, end_marker, lines in replacements:
            updated = _replace_block(updated, start_marker, end_marker, lines)
        if updated != text:
            touched.append(path)
            if not check:
                path.write_text(updated)
    return tuple(touched)


def check_registry_docs() -> tuple[Path, ...]:
    """Fail if any registry-backed doc block has drifted from its source registry."""
    touched = sync_registry_docs(check=True)
    if touched:
        formatted = "\n".join(path.relative_to(ROOT).as_posix() for path in touched)
        raise AssertionError(
            "registry-backed docs are out of sync:\n"
            f"{formatted}\n"
            "run `python -m bridge_reptends.sync_registry_docs`"
        )
    print("PASS docs::registry_sync")
    return touched


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="report drift and exit nonzero instead of rewriting files",
    )
    args = parser.parse_args(argv)

    if args.check:
        touched = sync_registry_docs(check=True)
        if touched:
            for path in touched:
                print(path.relative_to(ROOT))
            raise SystemExit(1)
        print("registry-backed docs already synchronized")
        return

    touched = sync_registry_docs()
    if touched:
        for path in touched:
            print(path.relative_to(ROOT))
        return
    print("registry-backed docs already synchronized")


if __name__ == "__main__":
    main()
