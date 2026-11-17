"""Build the published run proofs and enforce their source and axiom audit."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parent
hashes = json.loads((ROOT / "RadixResearch-source-hashes.json").read_text())
for name, digest in hashes.items():
    source = (ROOT / name).read_bytes()
    if hashlib.sha256(source).hexdigest() != digest:
        raise RuntimeError(f"Imported proof source changed without a provenance update: {name}")
    if re.search(rb"\bsorry\b|\badmit\b|^\s*axiom\b|\bnative_decide\b|skipKernelTC", source, re.M):
        raise RuntimeError(f"Proof bypass in {name}")

subprocess.run(["lake", "build", "RadixResearch"], cwd=ROOT, check=True)
audit = subprocess.run(["lake", "env", "lean", "RadixAudit.lean"], cwd=ROOT,
                       text=True, capture_output=True, check=True)
report = audit.stdout + audit.stderr
expected = re.findall(r"^#print axioms (\S+)", (ROOT / "RadixAudit.lean").read_text(), re.M)
entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", report, re.S)
if [name for name, _ in entries] != expected or len(expected) != 199:
    raise RuntimeError("The theorem audit is incomplete")
if re.search(r"\b(?:warning|error):", report):
    raise RuntimeError("Lean reported a warning or error during the axiom audit")
for name, axioms in entries:
    dependencies = {a.strip() for a in axioms.split(",") if a.strip()}
    if not dependencies <= {"propext", "Classical.choice", "Quot.sound"}:
        raise RuntimeError(f"Unexpected axiom dependency in {name}")
print(f"PASS {len(hashes)} unchanged proof sources and {len(entries)} theorem axiom checks.")
