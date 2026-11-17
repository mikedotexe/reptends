# Mixed radix proof provenance

The initial proof surface was imported on 2026-11-16 from `physics-math-research/research/reptend-bases/phase9`. The v1.2.0 audit covered 136 declarations, including 90 run and power declarations. The existing project uses the same Lean toolchain and Mathlib commit.

For v1.3.0, `RadixRuns/CarryBridge.lean` was adapted on 2026-11-16 from `physics-math-research/research/reptend-bases/phase11/lean/RadixRuns/CarryBridge.lean`. The original source SHA256 is `ff097c71984069ab4fcae033aa86240ee3d572d14431e7c47d76d3ef322039a9`. Its eleven theorem statements and proof bodies are unchanged. The import was narrowed from `RadixRuns.ReadingExamples` to `RadixRuns.Encoding`, which supplies all the required definitions without importing unrelated phase10 examples. Two base-general statements were added: `RadixRuns.indexed_remainder_general` and `RadixRuns.indexed_digit_general`. Their index is zero-based; the public tool's place k corresponds to n=k−1. The published module SHA256 is `9981530ff4218b2cee8c8877ce1651095a177408c7495ac70f6e499186022cb4`.

The original phase9 modules remain unchanged except that the `RadixRuns.lean` import barrel now includes `CarryBridge`. `RadixResearch-source-hashes.json` records the changed barrel and the new module; all other existing hash entries are preserved.

Run `python3 check_radix_proofs.py` from `lean/` to build and verify the 23 recorded source hashes and 149 theorem axiom checks. Only the standard logical dependencies `propext`, `Classical.choice`, and `Quot.sound` are permitted. These proofs establish the mathematical identities independently; they are not formal verification of the browser's JavaScript implementation.

The bracket and bar typography is explanatory notation. Run records, generated digits, value preservation, first-return certificates and convergence are formalized. A notation parser and universal return-existence theorem are outside this proof surface.
