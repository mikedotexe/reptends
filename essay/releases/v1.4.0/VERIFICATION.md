# Verification — essay v1.4.0

Published 17 November 2026 (Pacific time) at [Keep the pattern. Change the units.](https://reptends.mikedotexe.com/#change-radix).

- Reviewed source: [`3685354`](https://github.com/mikedotexe/reptends/commit/3685354c32a1951ec4152321d334ec0e752f9469).
- `index.html`: 196,222 bytes, SHA-256 `3becadb8b3665d803e72f959d6e0538b2d4563114969823195524ed861998fa7`.
- `robots.txt`: 613 bytes, unchanged SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`.
- [Release CI](https://github.com/mikedotexe/reptends/actions/runs/44044442090) passed Chromium, Firefox, WebKit and the Lean build/audit job.

## Arithmetic and proof checks

Strict TypeScript, 94 Node tests, 13 deployment-safety tests, standalone artifact validation, and `git diff --check` passed. The new tests independently generate both ordinary prefixes, check 338 continuation states, and exercise 7,140 positive-digit steps across denominators and remainders. They check legal digits, positive tails, unchanged prefixes, exact value accounting, local radix minimality, and a transient-return counterexample.

`python3 lean/check_radix_proofs.py` passed: 24 source hashes and 199 theorem axiom checks. The new public module imports all 50 phase13 statements and proof bodies unchanged. It includes the infinite continuation after an existing prefix. Allowed dependencies remain `propext`, `Classical.choice`, and `Quot.sound`. The browser code and the two starting-prefix computations are independently tested implementations, not formally verified programs.

## Browser and reading checks

Local Chromium and WebKit passed the complete suites; Linux CI also passed Firefox. The new checks cover both examples through eight changing-radix positions, exact state accounting, keyboard stepping, query bounds, preserved unrelated query parameters, Back/Forward, copied links and clipboard fallback. Both old run links and the Digit by Index chapter remain functional.

The main fourth chapter compares the first ordinary carried group with the new digit, then lets readers continue tripling or counting. Radices appear beneath bracketed digits. Place weights, exact integers and the general rule remain optional. The previous from-start power explorer is in a disclosure. Both examples remain explained without JavaScript. Screenshots at mobile and desktop widths were inspected; the counting continuation was also inspected in the in-app browser.

## Publication evidence

CloudFront invalidation `I643VP5D4ANG0OPMT6ILPPX2S5` completed. `python3 deploy/aws_site.py verify --target live`, `npm run test:live`, and `node deploy/check-dns.mjs` passed. The live browser confirmed 729, 2187, 6561, 19683 for 1/997 and 998, 999, 1000, 1001 for 1/998001, including exact state identities. Inherited controls passed with no additional asset requests or browser errors.

Trusted HTTPS serves the recorded artifact at the root, `/index.html`, and both tested progression links. HTTP redirects, ordinary DNS, and the private origin checks passed. The public handoff proof and proof atlas returned successfully. The published counting example was opened and inspected in the in-app browser.

The [manifest](manifest.json), [live receipt](live-verification.json), [shared links](shared-links.json), and [CI receipt](ci.json) preserve the evidence. The previous [v1.3.0 verification](../v1.3.0/VERIFICATION.md) remains available for rollback.

## Evidence boundaries

Fresh human-reader feedback remains pending. The broader repository's pre-existing generated-documentation drift is outside this change; the dedicated essay workflow is the release gate. No universally preferred notation or historical novelty is claimed. The continuation preserves the identified coefficient pattern with new weights; ordinary positional notation retains the exact value.
