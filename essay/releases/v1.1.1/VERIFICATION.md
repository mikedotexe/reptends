# Verification — essay v1.1.1

Published 8 October 2026 (Pacific time), following the independent AI reader review of v1.1.0.

- Source commit: [`fad656c`](https://github.com/mikedotexe/reptends/commit/fad656ce9e54cae1c70637a1795a36cc0b23dae4)
- `index.html`: 140,060 bytes, SHA-256 `0a28007f0bea7591e4523efae2b19b9d45cc5e47687f12984e7be93de398a105`
- `robots.txt`: 613 bytes, SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`
- [Three-browser source CI](https://github.com/mikedotexe/reptends/actions/runs/37841478344) passed for Chromium, Firefox, and WebKit.

## Reader-facing clarifications

The opening specimens now separate fixed-width groups with small visual gaps, preserving the exact continuous decimal text and preventing a group from splitting across lines. The main prose explains why multiplication by 1000 and by 3 leaves the same remainder modulo 997. A nearby native disclosure accounts for the entire omitted tail of the addition table, including the already-shown fractional part: 147/1000 + 531441/(997 × 1000) = 678/997 < 1.

The shared explorer marks all six decimal endpoints within its two grouped cycles. At group 56 it shows `7 | 00`, explains the remainder returning to 1 after the 7 and reaching 100 after the complete group, and offers the three digitwise equations. The other cut positions show `67 | 0` and `667 |`. All digits remain unchanged in text content. Keyboard announcements describe the boundary, and leaving a boundary removes its annotation. The inherited arithmetic engine is unchanged.

The main chapter structure and optional research guide remain intact. [README.md](README.md) records the bounded definition of done; [READER-CHECK.md](READER-CHECK.md) records the three AI reviews separately from pending human feedback.

## Exact arithmetic and browser checks

Strict TypeScript checking, 70 Node arithmetic/artifact/navigation tests, 13 deployment-safety tests, the standalone build, and `git diff --check` passed. CI ran these checks in each browser job. Three new tests compare decimal-return annotations to a continuous independent scan of all 996 decimal digits and cover all split offsets, trailing zeros, and inconsistent input rows. A fourth test independently checks the exact unfinished balance after the displayed stack and certifies that the first eleven groups cannot change.

Local Chromium and WebKit suites passed. The browser checks still cover all 332 selected positions, all existing carry and geometry interactions, sharing/history, native keyboard controls, reduced and normal motion, no-JavaScript examples, and offline operation without extra asset requests or browser errors. Added checks verify boundary note presence and cleanup across all positions, the `7 | 00` split and its three exact equations, accessible boundary announcements, and the static tail explanation. Desktop, tablet, and 320-pixel mobile screenshots of the separated opening groups and the expanded decimal-return note were inspected.

## Live verification

CloudFront invalidation `IC49AAVREURAKZYJAVUXN9VSYW` completed. `node deploy/check-dns.mjs`, `python3 deploy/aws_site.py verify --target live`, and `npm run test:live` passed against the exact published artifact. The live browser checks the split word, one-digit equations, final grouped remainder, and annotation cleanup alongside the existing interactions.

Ordinary IPv4/IPv6 DNS resolves. Valid HTTPS serves the reviewed bytes at `/`, `/index.html`, and the tested group query. HTTP returns 301 redirects for the essay and `robots.txt`, preserving the tested group query. Direct anonymous S3 requests for both objects return 403. No extra runtime asset requests or browser errors were observed.

The non-secret resource state and live receipt are in `deploy/hosting.json` and `deploy/live-verification.json`. The release manifest is [releases/v1.1.1/manifest.json](releases/v1.1.1/manifest.json).

## Outstanding evidence

Fresh human-reader feedback remains pending. The AI reviews do not establish comprehension by a human newcomer. The broader repository CI has its previously recorded generated-documentation and Yarn/Corepack issues; the dedicated essay workflow is this publication's release gate.
