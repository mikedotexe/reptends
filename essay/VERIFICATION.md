# Verification — essay v1.8.0

Published 22 November 2026 at [Where did the pattern go?](https://reptends.mikedotexe.com/#nearby-fractions).

- Reviewed source: [`5314ea0`](https://github.com/mikedotexe/reptends/commit/5314ea0a4b9048c0a39f19cb34400209e48c757e), merged through [PR #2](https://github.com/mikedotexe/reptends/pull/2) as `8100def`.
- `index.html`: 241,190 bytes, SHA-256 `5b00b19c5cee3e432d502d1615ff71942317c61520cb625336477164caea7523`.
- `robots.txt`: 613 bytes, unchanged SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`.
- [Dedicated release CI](https://github.com/mikedotexe/reptends/actions/runs/45049608785) passed Chromium, Firefox, WebKit, and the Lean build/audit on the reviewed source.

## The guided field lesson

The seventh chapter starts with the familiar powers in 1/997, reveals the 64 integer members from 969 through 1032, then places the same field on a square-root ruler. Its continuous boundary roots differ by exactly one. A slider and presets compare nearby fractions and both outside denominators; the actual six printed groups are calculated independently of the signed series terms. Borrowing above 1000 is explicit, and the exact boundary calculation is an optional disclosure.

The first six chapters and all existing explorers remain available. The field lesson preserves other URL parameters and restores shared selections. All three teaching stages remain readable without JavaScript.

## Arithmetic and proofs

Strict TypeScript, 112 Node tests, 13 deployment tests, standalone artifact validation, and whitespace checks passed. The new bounded model is tested against independent decimal long division for every displayed denominator from 968 through 1033, including terminating cases, and both membership failures immediately outside the field.

The [worked-example record](https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md#field-around-1000-worked-example) supplies the elementary derivation and distinguishes it from the tested browser implementation and the existing formal proofs. Integer arithmetic decides membership and printed groups; floating-point roots are used only for plotting. No general regime classification or universal width law is inferred from the displayed cases.

The unchanged Lean audit passed 26 source hashes and 257 theorem axiom checks locally and in release CI. The local audit used the existing canonical checkout’s build cache; all Lean source files were compared byte-for-byte with the release checkout. No Lean source or theorem changed.

## Browser and publication checks

The final artifact passed local Chromium and WebKit, including responsive layouts, keyboard operation, offline interaction, no-JavaScript reading, shared links, and Back/Forward restoration. All three hosted browser engines passed. Local Firefox failed in its launcher before loading the page; the hosted Firefox result verifies the reviewed source. The lesson was also visually inspected in the in-app browser at desktop and 320px widths.

Publication occurred at `2026-11-22T17:33:14.442417+00:00` UTC. CloudFront invalidation `I7NAZFAM488DDXP22M84RU7LK` completed. Live verification at `2026-11-22T17:34:23.426655+00:00` UTC matched the reviewed SHA-256 at both `/` and `/index.html`, checked the unchanged crawler policy and HTTPS redirects, and confirmed anonymous S3 denial. The live browser exercised all three field stages, positive and alternating examples, both integer boundaries, keyboard controls, the optional proof, and the existing progression and indexed-digit tools with no unexpected requests or runtime errors. The published chapter was opened in the in-app browser and returned to its first teaching step.

Release evidence: [manifest](releases/v1.8.0/manifest.json), [live receipt](releases/v1.8.0/live-verification.json), [live browser](releases/v1.8.0/live-browser.txt), [CI jobs](releases/v1.8.0/ci.json), [arithmetic tests](releases/v1.8.0/local-tests.txt), [local Chromium](releases/v1.8.0/local-chromium.txt), [local WebKit](releases/v1.8.0/local-webkit.txt), and [Lean audit](releases/v1.8.0/lean-audit.txt).

## Evidence boundaries

The field lesson is a scoped algebraic worked example and checked implementation, not a newly Lean-formalized theorem. Its integer members are not the continuous endpoints, and its square-root strip is not asserted to be centred on √1000. The lesson includes terminating reciprocals; membership describes the opening groups, not the period. Fresh human-reader feedback remains pending.

The separate [legacy CI](https://github.com/mikedotexe/reptends/actions/runs/45049631514) has the same failures as [v1.7 baseline CI](https://github.com/mikedotexe/reptends/actions/runs/44988411541): Yarn cache discovery precedes Corepack setup for the separate `site/` app, and the same six registry-generated files are stale. All six generated atlas blocks are byte-identical between `9f8978a` and `5314ea0`; the new worked example is an appendix outside those blocks. The dedicated essay release checks all passed. No workflow or protection settings were changed.
