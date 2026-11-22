# Verification — essay v1.7.0

Published 21 November 2026 (Pacific time; 2026-11-22T05:14:44.645831+00:00 UTC) at [Where did the pattern go?](https://reptends.mikedotexe.com/).

- Reviewed source: [`ebf371c`](https://github.com/mikedotexe/reptends/commit/ebf371cf7b5eaee58e1b3a4adf716c26ebf16830).
- `index.html`: 209,808 bytes, SHA-256 `dcfae56366465cfc057890897c3dbbc6721d824cbe65e582859f8b6c6f96b4f5`.
- `robots.txt`: 613 bytes, unchanged SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`.
- [Essay release CI](https://github.com/mikedotexe/reptends/actions/runs/44988411516) passed Chromium, Firefox, WebKit, and the Lean build/audit on the reviewed source.

## Reading path

The six chapters follow one question at a time: notice 729 becoming 731, add the overlapping powers, remember the remainder, recognize halfway and full returns, group a whole repeating block into one digit, and choose radices that keep the progression visible. Existing carry calculations, optional progression examples, notation, and indexed-digit tools remain available.

The new mirror explorer checks all 83 pairs in the base-1000 loop for 1/997. After group 83, remainder 996 starts the complementary half; after group 166, remainder 1 restarts the full loop. The ordinary 166-digit period and the 166-group loop are distinguished in an expandable explanation. The associated last power position is 3^165, with 3^0 counted first; the infinite progression continues beyond the group boundary.

The 1/7 example compares six decimal steps with one base-1,000,000 step, both returning to remainder 1. The radix chapter introduces the existing balance rule in plain language and works through choosing radix 998 before presenting the notation and controls.

## Arithmetic and proofs

Strict TypeScript, 106 Node tests, 13 deployment-safety tests, standalone artifact validation, and `git diff --check` passed. New checks compare every mirror pair against an independent 498-digit decimal walk, verify the first antipode and first return, and verify the packed 1/7 example with exact integers.

The Lean audit passed 26 unchanged source hashes and 257 theorem axiom checks. No Lean source or theorem changed. The new [mirror examples](https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md#remainder-mirror-examples) are labelled computed examples, with concrete algebra and explicit scope. Grouping references the existing run-accounting proof; radix selection references the existing balance-rule proof.

## Browser and publication checks

The final artifact passed local Chromium and WebKit and all three hosted browser engines. Local Firefox timed out in its launcher before loading the page; hosted Firefox passed on the same source. Checks cover the new pair controls, keyboard navigation, midpoint/full-return actions, responsive layouts, offline interaction, no-JavaScript reading, and the existing progression, history, sharing, and digit-index behavior. New chapters were visually reviewed at mobile and desktop widths, and the published whole-block chapter was inspected in the in-app browser.

CloudFront invalidation `IEJ2O8LIZOE618I51MTPA5N1ED` completed. Live checks verified the exact artifact at `/` and `/index.html`, the unchanged crawler policy, HTTPS redirects, and anonymous-origin denial. The live browser exercised the mirror controls, boundary actions, grouped-digit example, three retained progressions, and existing tools without unexpected asset requests or runtime errors.

Release evidence: [manifest](releases/v1.7.0/manifest.json), [live receipt](releases/v1.7.0/live-verification.json), [live browser checks](releases/v1.7.0/live-browser.txt), [CI jobs](releases/v1.7.0/ci.json), [local Chromium](releases/v1.7.0/local-chromium.txt), [local WebKit](releases/v1.7.0/local-webkit.txt), and [Lean audit](releases/v1.7.0/lean-audit.txt).

## Evidence boundaries

The mirror explorer and static examples are checked implementations, not newly formalized theorems. An even period alone does not guarantee complementary halves for arbitrary composite denominators; the optional explanation includes 1/21 as a counterexample. A matching complementary printed digit alone does not certify the halfway remainder. Fresh human-reader feedback remains pending.

The repository-wide [legacy CI](https://github.com/mikedotexe/reptends/actions/runs/44988411541) still reports the same unrelated failures as [baseline 57b60b0](https://github.com/mikedotexe/reptends/actions/runs/44205706138): the separate `site/` build invokes Yarn before Corepack is enabled, and generated registry documentation is out of sync. Those files and generated blocks were not changed by this release. The essay's dedicated release checks all passed.
