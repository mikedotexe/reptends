# Verification — essay v1.9.0

Published 22 November 2026 at [Give the pattern more room](https://reptends.mikedotexe.com/#power-and-grouping).

- Reviewed source: [`74fe652`](https://github.com/mikedotexe/reptends/commit/74fe652a8d2c0d9427da16a3676eccaefdd1e0e6), merged through [PR #4](https://github.com/mikedotexe/reptends/pull/4) as `4c4daa3`.
- `index.html`: 268,144 bytes, SHA-256 `c6ec06ede4fcfe4cfa7a1938a6e1609a665cf9009627ed4df48d0c7172965a07`.
- `robots.txt`: 613 bytes, unchanged SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`.
- [Dedicated release CI](https://github.com/mikedotexe/reptends/actions/runs/45052606803) passed Chromium, Firefox, WebKit, and the Lean build/audit on the reviewed source.

## Two separate experiments

The eighth chapter keeps the gap at 3 while moving through denominators 97, 997, 9997, 99997, and 999997. Readers see 4, 6, 8, 10, and 12 unchanged groups, then predict and reveal the first carry. Ordinary field widths and integer counts grow while the square-root boundaries stay exactly one apart. Rounded boundary labels are explicitly approximate.

A separate control fixes 1/997 and partitions its same sixty decimal digits into groups of three through six. It displays the actual quotient seed q and ordinary remainder k, giving coefficients q*k^j. The changed grouping does not promise a monotonically longer clear opening. Optional explanations give the exact threshold, the root-width algebra, and the natural endpoints. The 166-digit decimal period is distinguished from 166 three-digit groups, which span three copies of that period.

Prior chapters and tools remain available. Both controls preserve the other query parameters, restore shared URL/history state, and support keyboard operation. The default worked examples and carry answer remain readable without JavaScript.

## Arithmetic and proofs

Strict TypeScript, 117 Node tests, 13 deployment tests, standalone artifact validation, and whitespace checks passed. Independent decimal long division verifies all five family widths and all four fixed-denominator groupings, including q greater than one. Integer membership independently determines the field endpoints/counts; floating-point roots only supply drawing coordinates.

The [worked-example record](https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md#power-dial-and-fixed-grouping-examples) scopes the lesson, cites the registered positive-quotient series and incoming-carry identities, and states the elementary field derivation. This browser implementation is independently tested, not Lean-certified. No proof source or registry claim changed.

The unchanged Lean audit passed 26 registered source hashes and 257 theorem axiom checks locally and in release CI. The local audit used the canonical checkout's cached build; all 56 Lean source files in the release checkout were compared byte-for-byte with that checkout.

## Browser and publication checks

The final artifact passed local Chromium and WebKit and all three hosted engines. Checks cover mobile/desktop layouts, keyboard controls, every dial value, first-carry predictions, independent experiment state, history/bounds, offline interaction, and no-JavaScript reading. Local Firefox was not rerun because its launcher failed before page load in the previous release; hosted Firefox passed this reviewed commit. The in-app browser was visually checked at its reading width and at 320px.

Publication occurred at `2026-11-22T18:05:27.090692+00:00` UTC. CloudFront invalidation `IBUKK8T6R36WYLCFI825F8WMMA` completed. Live verification at `2026-11-22T18:06:32.581379+00:00` UTC matched the exact reviewed hash at `/` and `/index.html`, checked the crawler policy and HTTPS redirect, and confirmed anonymous S3 denial. The live browser exercised both new controls and the existing field, progression, and indexed-digit tools without unexpected requests or runtime errors. The published lesson was opened in the in-app browser and its 1/9997 carry prediction was checked visually.

Release evidence: [manifest](releases/v1.9.0/manifest.json), [live receipt](releases/v1.9.0/live-verification.json), [live browser](releases/v1.9.0/live-browser.txt), [CI jobs](releases/v1.9.0/ci.json), [arithmetic tests](releases/v1.9.0/local-tests.txt), [local Chromium](releases/v1.9.0/local-chromium.txt), [local WebKit](releases/v1.9.0/local-webkit.txt), and [Lean audit](releases/v1.9.0/lean-audit.txt). Earlier release evidence remains in `releases/v1.8.0/`.

## Evidence boundaries

The new lesson is a bounded implementation and algebraic worked example. Integer field members are distinct from continuous boundaries. Grouping a fixed fraction changes its seed and multiplier; increasing the power in the fixed-gap family changes the fraction. Fresh human-reader feedback remains pending.

The separate [legacy CI](https://github.com/mikedotexe/reptends/actions/runs/45052619516) retains the prior failures documented in v1.8.0: Yarn cache discovery before Corepack for the separate `site/` app, and the same six out-of-sync registry-generated files. All generated proof-atlas blocks and the other affected files are unchanged; the new worked-example record is an appendix outside those blocks. Dedicated essay release checks all passed. No workflow or protection settings changed.
