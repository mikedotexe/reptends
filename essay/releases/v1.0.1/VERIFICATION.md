# Verification — essay v1.0.1

Published 6 October 2026 (Pacific time). The current standalone artifact is 75,438 bytes, SHA-256 `29a50ae4f9efda6f9ced09ec13298d8adf0afe10c58c51f3c831f602f2eca425`.

The tested source commit is [`64df4ed`](https://github.com/mikedotexe/reptends/commit/64df4ed8b46301cb50f7f9d083d5b3bf04feb838). Later release-record commits do not change the built page. The original first-edition artifact and its [verification record](releases/v1.0.0/VERIFICATION.md) are preserved in `releases/v1.0.0/`.

## Arithmetic and reader-facing changes

- 38 arithmetic, artifact, and navigation tests pass; strict TypeScript checking and the single-file build pass.
- All 332 main positions agree with ordinary division; all 333 finite boundaries balance exactly. The three inherited arithmetic modules remain byte-for-byte copies of their research source.
- The tail explanation states its units explicitly: at the seventh group, the later contributions total `2187/997 = 2 + 193/997`. The whole 2 changes 729 to 731. The following printed group is 193 after the previous-carry adjustment.
- The minimal decimal period remains 166 digits; 166 three-digit groups span 498 decimal positions.
- Mike's signed origin note uses his supplied account of the widening groups and “number salad.” Source and feedback links point to the public repository.
- Shared links use group numbers 1–332, reject malformed/ambiguous input, preserve linked positions through browser history, and offer a selectable input when clipboard access is unavailable.

## Browser verification

[Essay browser checks passed](https://github.com/mikedotexe/reptends/actions/runs/37549631826) on Ubuntu 24.04 for Chromium 151, Firefox 153, and WebKit 26.5. Each job passed all 38 tests, typechecking, build, and its browser suite. Local Chromium and WebKit suites also passed.

Coverage includes narrow/mobile, tablet, and desktop layouts; keyboard controls; reduced and normal motion; every curated geometry slice; initial zero groups; large-integer disclosures; no-JavaScript content; shared-link bounds, clipboard success/fallback, and Back/Forward; and zero additional asset requests or browser errors. Chromium checks every one of the 332 UI positions. WebKit loads the local file before enabling Playwright's offline emulator, then performs all interactions offline; its file-navigation limitation does not affect the self-contained artifact.

WebKit provides coverage of Safari's engine, not a separate native Safari application test. The local Firefox build cannot start on this macOS version; the passing Linux Firefox job supplies that coverage. Carry, personal-note, and sharing-fallback screenshots at 320 and 1440 px were visually inspected under `qa/`.

## Publication, DNS, and access

The narrowed `reptends` profile uploaded only `index.html`; CloudFront invalidation completed. Ordinary system DNS now resolves without overrides, with both A and AAAA records. `node deploy/check-dns.mjs` and `npm run test:live` pass:

- Trusted HTTPS returns the exact reviewed artifact at `/`, `/index.html`, and `/?group=8`.
- HTTP returns 301 to HTTPS while preserving the group query.
- An unmodified Chromium visit to `http://reptends.mikedotexe.com/?group=8#carry` reaches the HTTPS URL, retains the fragment, and selects group 8 with output 193.
- The live reveal, next/reset, 166-group jump, and cube controls work without extra requests or browser errors.
- Anonymous S3 access remains denied with 403. The deployer retains only this object's upload permission and this distribution's invalidation permissions.

Current deployment IDs and evidence are in `deploy/hosting.json` and `deploy/live-verification.json`; the [release manifest](releases/v1.0.1/manifest.json) records the source commit, artifact hash, and browser run.

## Outstanding evidence and inherited repository checks

Actual fresh-reader feedback is **pending**. [READER-CHECK.md](READER-CHECK.md) supplies the short, uncoached protocol and a blank response record. Neither an AI review nor browser automation is reported as human comprehension evidence.

The separate, older [repository CI](https://github.com/mikedotexe/reptends/actions/runs/37549631750) has pre-existing failures outside the essay: Yarn 1.22.22 is invoked during cache setup before Corepack enables the old site's required Yarn 4.12.0, and six generated research documentation surfaces have registry drift. The baseline `ae9f4d9` has the same Site Build annotation; comparing both commits with the unchanged registry renderer produces the same six documentation mismatches. The old research code, site, Lean files, and CI workflow were not changed by this release.
