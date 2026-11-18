# Verification — essay v1.6.0

Published 17 November 2026 (Pacific time; 2026-11-18T00:08:24.632456+00:00 UTC) at [Keep the pattern. Change the units.](https://reptends.mikedotexe.com/#change-radix).

- Reviewed source: [`28c0e33`](https://github.com/mikedotexe/reptends/commit/28c0e33e8739a6b2e4dc2794db563591ae27192c).
- `index.html`: 192,828 bytes, SHA-256 `f2695acf97cc43cf18653d03e2ed8a9148f56334ea2601deb2fde3fdb7991e76`.
- `robots.txt`: 613 bytes, unchanged SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`.
- [Release CI](https://github.com/mikedotexe/reptends/actions/runs/44203722926) passed Chromium, Firefox, WebKit, and the Lean build/audit. The first Firefox attempt stalled while installing dependencies and was cancelled before application checks. Its retry passed on the same source commit; the other three successful jobs were retained.

## Arithmetic, notation, and proofs

Strict TypeScript, 103 Node tests, 13 deployment-safety tests, standalone artifact validation, and `git diff --check` passed. New checks cover weighted run evaluation, equivalent split runs, initial zeros, the complete counting prefix, legal digits, independent long division through every serialized example, theorem-name references, and JSON round trips.

The Lean audit passed 26 unchanged source hashes and 257 theorem axiom checks. The [registered proof map](https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md#mixed_radix_run_value_preservation) connects run weights to `Encoding.lean` and `Core.lean`; [the balance claim](https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md#unified_balance_rule) connects choices, completion and stream convergence to `BalanceRule.lean`. No Lean source or theorem was changed. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed dependencies.

The notation uses angle brackets for successive digits sharing a radix, commas for digit positions, and bars for radix changes. The page and standalone `NOTATION.md` specify exact weights and distinguish a radix change from a remainder return. Complete generators, digits and eight changed steps per example are embedded in non-executable JSON. This data is independently checked, not a proof-assistant certificate.

## Browser and reading checks

The final artifact passed local Chromium and WebKit, and all three hosted engines. Tests cover the preserved run and eight changed steps of all three examples, signed balances, completion, legal sharing/history, keyboard operation, offline operation, no-JavaScript reading, and mobile/desktop layouts. All three full inscriptions and the optional proof reference were visually inspected at mobile and desktop widths. No unexpected asset requests or runtime errors occurred.

The opening now concentrates on 1/997. Geometry and broad polynomial-recurrence digressions were removed from the reading path, and digit lookup became an optional tool after the conclusion. The three main examples are tripling (1/997), Fibonacci (1/9899), and counting (1/998001). Earlier arithmetic sources and shared links remain available.

## Publication evidence

CloudFront invalidation `I53XMSF6R5G45O2V0TK8MJUXLE` completed. Live checks verified the exact artifact at `/` and `/index.html`, the unchanged crawler policy, HTTPS redirects, DNS, and anonymous-origin denial. The live browser exercised all three progressions, the notation data and proof reference, indexed digits, disclosures and exact state identities. Four shared result URLs served the checked artifact; all five public notation/proof links returned 200. The published three-example comparison was inspected in the in-app browser.

Release evidence: [manifest](manifest.json), [live receipt](live-verification.json), [live browser checks](live-browser.txt), [DNS](dns-verification.txt), [shared links](shared-links.json), and [CI receipt](ci.json).

## Evidence boundaries

The notation renderer, complete initial-prefix computations, JSON serializer, and browser are tested implementations, not formally verified programs. The generic stream theorem assumes positive targets after any separately certified initial zeros, and pads with zero digits after completion. A rejected zero target needs separate feasibility analysis. The supplied progression is not uniquely selected by the fraction. Fresh human-reader feedback remains pending.
