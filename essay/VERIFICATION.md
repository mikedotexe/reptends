# Verification — essay v1.5.0

Published 17 November 2026 at [Keep the pattern. Change the units.](https://reptends.mikedotexe.com/#change-radix).

- Reviewed source: [`60a3bba`](https://github.com/mikedotexe/reptends/commit/60a3bbaff35983ded45a52450e153b611e8ec677).
- `index.html`: 200,931 bytes, SHA-256 `b3ac5afaa4347ec94b76e93cee1006215e41ee015b9c734d0c9081c8347ebd67`.
- `robots.txt`: 613 bytes, unchanged SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`.
- [Release CI](https://github.com/mikedotexe/reptends/actions/runs/44130498749) passed Chromium, Firefox, WebKit, and the Lean build/audit job.

## Arithmetic and proofs

Strict TypeScript, 98 Node tests, 13 deployment-safety tests, standalone artifact validation, and `git diff --check` passed. The new tests independently reconstruct the Fibonacci prefix, check its continuation and the three switching boundaries, and compare 26,400 balance decisions against ordinary integer division. They include positive, negative, oversized and zero trial balances; 1/8 completes at 0.125. Existing progression and indexed-digit tests continue to pass.

The Lean audit passed 26 recorded source hashes and 257 theorem axiom checks. `BalanceRule.lean` proves the signed decision, legal digits, exact prefix and value preservation, completion, zero padding, and convergence of the written stream. `BalanceContinue.lean` provides the positive continuation core and concrete witnesses. All previously published substantive proof modules remain unchanged. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed dependencies. The stream theorem assumes positive targets after any separately certified initial zeros. Rejected zero targets require separate feasibility analysis. The TypeScript implementation and full starting-prefix computations are independently tested, not formally verified.

## Browser and reading checks

The final artifact passed local Chromium and all three hosted engines. WebKit also passed locally before the final small wording/notation edit. Tests cover three examples at nine positions each (last kept step and eight changed steps), exact value accounting, a signed negative balance, termination prose, query bounds, Back/Forward, sharing and clipboard fallback, keyboard controls, offline operation, no-JavaScript reading, and mobile/desktop layouts. Existing run links and indexed-digit controls remain valid. Mobile and desktop Fibonacci screenshots were inspected.

The chapter explains the next supplied term, trial leftover, keep/change decision, and actual next remainder. Proofs and exact integers remain optional. A separate completion disclosure shows `1/8 = 0.[1]₁₀[2]₁₀[5]₁₀`, with remainder zero and optional zero padding. The published completion explanation and Fibonacci negative balance were inspected in the in-app browser.

## Publication evidence

CloudFront invalidation `I6H3TU0BLHRBP0GBU8LIANULD7` completed. Live artifact verification, live browser tests, DNS, redirects, and private-origin checks passed. The live explorer confirmed the first four continuation steps of all three examples, including exact state identities. Four shared result URLs served the exact artifact; the public proof and atlas returned 200. No additional asset requests or browser errors occurred.

The [manifest](releases/v1.5.0/manifest.json), [live receipt](releases/v1.5.0/live-verification.json), [shared links](releases/v1.5.0/shared-links.json), and [CI receipt](releases/v1.5.0/ci.json) preserve the evidence. The previous [v1.4.0 verification](releases/v1.4.0/VERIFICATION.md) remains available for rollback.

## Evidence boundaries

Fresh human-reader feedback remains pending. The root pytest suite was unavailable in the local Python environment; the registry was separately checked for preservation of all existing records, unique IDs and valid new evidence links. The broader repository's pre-existing generated-documentation drift is outside this change; the dedicated essay workflow is the release gate. The supplied progression is not uniquely selected by the fraction. Changing radices changes later digit weights; ordinary positional notation retains the exact value.
