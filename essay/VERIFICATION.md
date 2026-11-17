# Verification — essay v1.3.0

Published 16 November 2026 (Pacific time) at [Digit by Index](https://reptends.mikedotexe.com/#digit-index).

- Reviewed source: [`f87869d`](https://github.com/mikedotexe/reptends/commit/f87869d06da1e4c314e780113d898a776d399a75).
- `index.html`: 177,413 bytes, SHA-256 `50c1a7f654d3e90bff2b32aa128e1f80330acc2a5a9e22e09523d4dae547e0fe`.
- `robots.txt`: 613 bytes, unchanged SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`.
- [Release CI](https://github.com/mikedotexe/reptends/actions/runs/44035206341) passed Chromium, Firefox, WebKit and the Lean build/audit job.

## Arithmetic and proof checks

Strict TypeScript, 87 Node tests, 13 deployment-safety tests, standalone artifact validation, and `git diff --check` passed. The new core compares 62,496 indexed positions with independent sequential division and checks huge indices against independently discovered remainder orbits. Tests include nondecimal bases, non-1 and improper numerators, zero, termination, parser allocation limits, ranges, cancellation and mismatches.

`python3 lean/check_radix_proofs.py` passed: 23 source hashes and 149 theorem axiom checks. The new public carry bridge preserves its phase11 statements and proofs, with a narrower import, and adds two arbitrary-base indexed formulas. Allowed dependencies remain `propext`, `Classical.choice` and `Quot.sound`. The browser code is not formally verified.

## Browser and reading checks

Local Chromium and WebKit passed the complete browser suites. Checks include huge-index lookup, group 167 returning `001`, the exact `3^166` power/carry display, base 16, improper fractions, terminating and zero expansions, independent sequential confirmation, stopped/edited/replaced jobs, input bounds, clipboard fallback, preserved query parameters and Back/Forward navigation. Mobile and desktop screenshots of the new chapter were inspected. The complete essay remains self-contained and readable without JavaScript; enhanced controls are hidden when inactive.

The main reading path now has five chapters. The new chapter leads with a concrete fraction and position, then offers the exact power and general identity in optional disclosures. Fable is credited on the page and the original attachment hash is recorded in the release notes.

## Publication evidence

CloudFront invalidation `IV14RN2KX3KSNCBBXUJGKTQTE` completed. `python3 deploy/aws_site.py verify --target live`, `npm run test:live`, and `node deploy/check-dns.mjs` passed. The live browser verified group 167’s `001`, the full `3^166` and carry values, an independent sequential confirmation, and the digit `6` at position `10^100` of 1/9899. It also checked the inherited controls, with no additional asset requests or browser errors.

Trusted HTTPS serves the recorded artifact at the root, `/index.html`, and both tested indexed-result links. HTTP redirects and ordinary IPv4/IPv6 DNS passed. Direct anonymous S3 access returns 403 for both objects. The public carry-proof source and proof atlas returned successfully. The published 997 result link was also opened and inspected in the in-app browser.

The [manifest](releases/v1.3.0/manifest.json), [live receipt](releases/v1.3.0/live-verification.json), [shared links](releases/v1.3.0/shared-links.json) and [CI receipt](releases/v1.3.0/ci.json) preserve the evidence. The previous [v1.2.0 verification](releases/v1.2.0/VERIFICATION.md) preserves the earlier publication for rollback.

## Evidence boundaries

Fresh human-reader feedback remains pending. The broader repository’s pre-existing generated-documentation drift is outside this change; the dedicated essay workflow is the release gate. No universally preferred notation is claimed. A repeated remainder identifies the ordinary fixed-base cycle; an unbounded power and a changing-radix digit use distinct accounting and place weights.
