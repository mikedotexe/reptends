"""
Sync registry-backed Markdown blocks into public docs.

This keeps selected outward surfaces derived from the machine-readable claim and
vocabulary registries rather than maintained by hand.
"""

from __future__ import annotations

from collections.abc import Iterable
from pathlib import Path

from .registry import (
    render_claim_table_lines,
    render_open_claim_lines,
    render_registry_summary_lines,
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
        ),
        ROOT / "docs" / "PROOF_STATUS_ATLAS.md": (
            ("<!-- REGISTRY_SUMMARY_START -->", "<!-- REGISTRY_SUMMARY_END -->", render_registry_summary_lines()),
            ("<!-- CLAIM_TABLE_START -->", "<!-- CLAIM_TABLE_END -->", render_claim_table_lines()),
            ("<!-- OPEN_CLAIMS_START -->", "<!-- OPEN_CLAIMS_END -->", render_open_claim_lines()),
        ),
        ROOT / "docs" / "VOCABULARY.md": (
            ("<!-- VOCABULARY_TABLE_START -->", "<!-- VOCABULARY_TABLE_END -->", render_vocabulary_table_lines()),
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
