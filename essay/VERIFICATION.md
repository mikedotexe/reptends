# Verification — essay v1.1.0

Published 8 October 2026 (Pacific time), following v1.0.5.

- Source commit: [`45abb8c`](https://github.com/mikedotexe/reptends/commit/45abb8c4b97fcf866085471720590a012fd6c594)
- `index.html`: 135,317 bytes, SHA-256 `46fbad883f6178ebb0c97de3c8dfd1315290c13b12c803e68761906b9a426e00`
- `robots.txt`: 613 bytes, SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`
- [Three-browser source CI](https://github.com/mikedotexe/reptends/actions/runs/37837723245) passed for Chromium, Firefox, and WebKit. Firefox alone was retried after slow Ubuntu package downloads; the source commit did not change.

## Reading path and verification guide

The main story now proceeds from the actual decimal jumble through stacked addition, a unified power/remainder/printed-group explorer, and a standalone “When have we seen enough?” chapter. Controls sit beside the values they change. The carry inspector, remainder-split animation, base-3 discovery, general recurrence notes, and square/cube geometry remain available as native disclosures. Canonical shared-group links now land at `#repeat`; incoming `#carry` links retain their selected group.

The guide states assumptions and indexing, derives the carry identity and exact finite-prefix balance, and supplies a dependency-free Python verifier. The built HTML also contains `script#reptends-certificate`, a non-executable JSON record with all four complete decimal and word cycles, returning-state witnesses, power positions, first carries, and exact finite-prefix accounting. The JSON distinguishes computed evidence from proof-assistant certification. Proof-status links identify registered results and their scope. The three inherited arithmetic modules remain unchanged.

## Exact arithmetic and browser checks

Strict TypeScript checking, 66 Node arithmetic/artifact/navigation tests, 13 deployment-safety tests, the standalone build, and `git diff --check` passed. CI ran these checks in each browser job. Six new tests independently check the four-case certificate and execute the displayed Python program. Existing checks still cover all 332 main transitions and all 333 finite boundaries.

Browser regression checks cover all 332 ordinary-division readouts, cycle return, all three endpoint jumps, query links and browser history, keyboard focus and native disclosures, proof deep links, the four-case JSON, complete large integers, reduced and normal motion, and the square/cube controls. Layouts at 320, 360, 768, and 1440 pixels were tested as applicable; the page stays within its viewport, and wide tables remain reachable by horizontal scrolling. Static examples and disclosures also work with JavaScript disabled.

Local Chromium and WebKit suites passed. Desktop, tablet, and mobile screenshots were inspected, including the opening, unified readouts, finite-description chapter, and complete large values. The revised local page was additionally inspected and operated in the in-app browser at desktop and 390-pixel mobile widths. Offline interaction checks detected no additional runtime asset requests or browser errors.

## Live verification

CloudFront invalidation `I1L7CUNH91PDD04XLXU91VH5CN` completed. `node deploy/check-dns.mjs`, `python3 deploy/aws_site.py verify --target live`, and `npm run test:live` all passed against the published artifact.

Ordinary IPv4/IPv6 DNS resolves. Valid HTTPS serves the exact reviewed bytes at `/`, `/index.html`, and the tested group query. HTTP returns 301 redirects for the essay and `robots.txt`, preserving the tested group query. Direct anonymous S3 requests for both objects return 403. The live browser confirms the three-view explorer, 166-group return, endpoint jumps, optional disclosures, JSON evidence, verifier link, and geometry controls, with no extra asset requests or browser errors.

The non-secret resource state and live receipt are in `deploy/hosting.json` and `deploy/live-verification.json`. The release manifest is [releases/v1.1.0/manifest.json](releases/v1.1.0/manifest.json).

## Outstanding evidence

Fresh-reader feedback remains pending; [READER-CHECK.md](READER-CHECK.md) now explicitly asks whether the powers stop when the repeating block ends. Automated and AI review do not substitute for human comprehension evidence. The broader repository CI has its previously recorded generated-documentation and Yarn/Corepack issues; the dedicated essay workflow is this publication's release gate.
