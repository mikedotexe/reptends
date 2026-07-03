from pathlib import Path

from bridge_reptends import load_lean_claim_carriers


ROOT = Path(__file__).resolve().parent.parent
THEOREM_GUIDE = ROOT / "lean" / "THEOREM_GUIDE.md"


def test_digit_periodicity_claim_carrier_lists_executable_bridge_theorem() -> None:
    carrier = next(
        record
        for record in load_lean_claim_carriers()
        if record.claim_id == "digit_periodicity"
    )

    assert "digitAt_orbitRem_eq" in carrier.theorem_names


def test_theorem_guide_digit_periodicity_row_mentions_executable_bridge_theorem() -> None:
    row = next(
        line
        for line in THEOREM_GUIDE.read_text().splitlines()
        if line.startswith("| `digit_periodicity` |")
    )

    assert "`digitAt_orbitRem_eq`" in row
