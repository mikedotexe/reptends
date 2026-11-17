# Verification — essay v1.3.0

Prepared for publication at [Digit by Index](https://reptends.mikedotexe.com/#digit-index). Final publication receipts will be recorded after the release checks and deployment.

## Arithmetic and proof checks

Strict TypeScript, 87 Node tests, 13 deployment-safety tests, standalone artifact validation, and `git diff --check` passed. The new core compares 62,496 indexed positions with independent sequential division and checks huge indices against independently discovered remainder orbits. Tests include nondecimal bases, non-1 and improper numerators, zero, termination, parser allocation limits, ranges, cancellation and mismatches.

`python3 lean/check_radix_proofs.py` passed: 23 source hashes and 149 theorem axiom checks. The new public carry bridge preserves its phase11 statements and proofs, with a narrower import, and adds two arbitrary-base indexed formulas. Allowed dependencies remain `propext`, `Classical.choice` and `Quot.sound`. The browser code is not formally verified.

## Browser and reading checks

Local Chromium and WebKit passed the complete browser suites. Checks include huge-index lookup, group 167 returning `001`, the exact `3^166` power/carry display, base 16, improper fractions, terminating and zero expansions, independent sequential confirmation, stopped/edited/replaced jobs, input bounds, clipboard fallback, preserved query parameters and Back/Forward navigation. Mobile and desktop screenshots of the new chapter were inspected. The complete essay remains self-contained and readable without JavaScript; enhanced controls are hidden when inactive.

The main reading path now has five chapters. The new chapter leads with a concrete fraction and position, then offers the exact power and general identity in optional disclosures. Fable is credited on the page and the original attachment hash is recorded in the release notes.

## Publication evidence

Pending the Linux release workflow and live deployment. The previous [v1.2.0 verification](releases/v1.2.0/VERIFICATION.md) preserves the earlier publication for rollback.

## Evidence boundaries

Fresh human-reader feedback remains pending. The broader repository’s pre-existing generated-documentation drift is outside this change; the dedicated essay workflow is the release gate. No universally preferred notation is claimed. A repeated remainder identifies the ordinary fixed-base cycle; an unbounded power and a changing-radix digit use distinct accounting and place weights.
