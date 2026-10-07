# Verification — essay v1.0.2

The standalone artifact is 87,269 bytes, SHA-256 `dde4805aede619f3520c196673c921a997d88caa74edb172a5b5943457898ee9`. The tested source commit is [`14fa261`](https://github.com/mikedotexe/reptends/commit/14fa261a1282458659e8375fd763fc210d78fb0c). Later release-record commits do not change the built page. Earlier verification records are preserved under `releases/v1.0.0/` and `releases/v1.0.1/`.

## Opening comparison

The essay now begins with sixteen actual decimal groups each of 1/97, 1/997, and 1/9997. Their first four, six, and eight groups respectively follow powers of three. The first corrections are 81 → 83, 729 → 731, and 6561 → 6562. Each example continues into later groups before the reader reaches the focused 1/997 explanation.

The preserved exact recurrence engine generates these examples at build time. Independent digit-by-digit long division checks every displayed digit, including initial zeros and correction boundaries. The comparison is present in the standalone HTML and readable without JavaScript. Text labels, solid/dotted borders, and an outline accompany its colors.

The 1/997 comparison now shows 731 immediately. Its explanation button selects group 7, scrolls to the carry explanation, and moves keyboard focus to that section. Shared-group links and the main position control retain their existing behavior.

## Arithmetic and browser verification

All 42 arithmetic, artifact, and navigation tests pass, along with strict TypeScript checking and the standalone build. The three inherited arithmetic modules are unchanged. All 332 main positions and 333 finite boundaries retain their exact division and residual checks; the minimal decimal period remains 166 digits, while 166 three-digit groups span 498 decimal positions.

Local Chromium and WebKit full browser suites passed against this artifact. Gallery crops were visually inspected at 320, 768, and 1440 px, including 320 px without JavaScript. All sixteen groups in every example remain visible and wrap only between groups. The checks also cover keyboard navigation, reduced and normal motion, geometry, large integers, shared links and history, clipboard fallback, and absence of external asset requests and browser errors.

[GitHub browser checks passed](https://github.com/mikedotexe/reptends/actions/runs/37555219636) on Ubuntu 24.04 for Chromium, Firefox, and WebKit. Every job passed the 42 tests, typechecking, build, and its browser suite. All three CI builds produced the same 87,269-byte standalone file size as the reviewed local artifact.

WebKit covers Safari's engine, not a separate native Safari application test. The local Firefox build cannot start on this macOS version; Linux CI supplies Firefox coverage.

## Publication

Published 6 October 2026 (Pacific time), with CloudFront invalidation completed. The narrowed deployer uploaded only `index.html`. `node deploy/check-dns.mjs`, `python3 deploy/aws_site.py verify --target live`, and `npm run test:live` passed: ordinary DNS resolves; trusted HTTPS serves the exact reviewed artifact at `/`, `/index.html`, and `/?group=8`; HTTP returns 301 to HTTPS while preserving the group query; anonymous S3 access returns 403. Live controls work without additional asset requests or browser errors. Refreshing the existing in-app browser tab visibly confirmed all three opening examples followed by the 1/997 explanation.

Current resource IDs and publication evidence are in `deploy/hosting.json` and `deploy/live-verification.json`. The release manifest is `releases/v1.0.2/manifest.json`.

## Outstanding evidence

Fresh-reader feedback remains pending; the protocol is in [READER-CHECK.md](READER-CHECK.md). Automated or AI checks do not substitute for human comprehension evidence. The older repository CI has unrelated, pre-existing Yarn bootstrap and generated-documentation failures, documented in the [v1.0.1 verification record](releases/v1.0.1/VERIFICATION.md); this change does not modify that research code or workflow.
