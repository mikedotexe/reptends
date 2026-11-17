# Essay v1.2.0

Prepared 16 November 2026. Publication evidence is recorded in `manifest.json` after live verification.

The essay now has four chapters: carrying, repeating remainders, finite descriptions, and changing radices. Chapter 04, “Let the measuring units grow,” keeps 1/997 fixed while using radices 997·3^n+1 to display each power 3^n as a legal digit. Every one-digit run is a first return to remainder 1. A focused explorer covers exponents 0–168 and supports independent share links. The opening notation and first four accumulated values remain readable without JavaScript.

Shorter introductions and transitions keep the reading path approachable. Exact state inspection, decimal conversion and the general proof sit behind native disclosures. The existing decimal/carry and geometry explorations retain their arithmetic and controls. The prose explicitly limits identical future digits after a remainder return to a fixed radix.

The imported Lean modules preserve their original sources and dependency versions. They prove arbitrary finite run and radix-change value preservation, legal power digits, first-return certificates, nontermination of the chosen representation, and an actual infinite sum of 1/D. Source hashes and a 136-theorem axiom audit are enforced by `lean/check_radix_proofs.py`. The proof-status atlas registers the two public claim families. The broader recurrence framework's open claims are unchanged.

Local checks: strict TypeScript; 76 Node tests; 13 deployment-safety tests; standalone artifact validation; source provenance and all 136 theorem dependency checks; Chromium and WebKit browser suites. Mobile and desktop screenshots were inspected. Firefox's local macOS headless process failed to initialize; the Linux Firefox workflow is a required release check. Real-reader feedback remains pending.

The broader repository has pre-existing generated-documentation drift, verified before the new claim registration. The release changes only affected summary blocks and adds the two new atlas rows with portable proof links. The dedicated essay workflow, including its Lean job, is this edition's release gate.
