# Verification — essay v1.0.5

Published 8 October 2026 (Pacific time), on top of the completed v1.0.4 revision.

- Source commit: [`669cb92`](https://github.com/mikedotexe/reptends/commit/669cb921f2b78bf5676028582a43b2b453029694)
- `index.html`: 107,654 bytes, SHA-256 `e05657150986d1308f0139472f9394c509c52f6a2bb03f4460c260dbdcc52649`
- `robots.txt`: 613 bytes, SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`
- [Three-browser source CI](https://github.com/mikedotexe/reptends/actions/runs/37834467412) passed for Chromium, Firefox, and WebKit.

## Reader-facing addition

The “When have we seen enough?” panel follows the synchronized remainder readouts. It distinguishes three landmarks for 1/997: the first carry at group 7 (`3^6`, printing `731`), the first decimal return at digit 166 (group 56, `3^55`, split `7 | 00`), and the aligned word return at group 166 (`3^165`, ending `667`). Its three keyboard-accessible buttons select the existing shared playhead and move focus to the readouts.

The native comparison disclosure covers 97, 997, 94, and 994. It keeps the initial nonrepeating zero and startup word for 94 and 994 explicit, uses powers of 6 for those denominators, counts from exponent zero, and distinguishes a finite description of the repeating decimal from truncation of the geometric series. Returning remainder witnesses and complete power values are available without JavaScript.

## Exact arithmetic and browser checks

Strict TypeScript checking, 60 Node arithmetic/artifact/navigation tests, 13 deployment-safety tests, the standalone build, and `git diff --check` passed. Each of the three Linux CI jobs independently ran these checks and its browser suite.

The 14 added arithmetic checks discover the decimal and grouped cycles independently, compare every grouped word to digitwise long division, verify split boundaries and startup counts, and retain the exact nonzero geometric tail at each endpoint. Existing checks still cover all 332 main transitions and all 333 finite boundaries.

Local Chromium and WebKit suites passed at mobile, tablet, and desktop widths. Checks cover the new jump buttons and focus destination, boundary comparison values, accessible table headings, all columns reachable on narrow screens, native disclosures with and without JavaScript, exact large integers, reduced motion, and no runtime asset requests or browser errors. Desktop and mobile screenshots of the new panel and the expanded comparison were inspected. The no-JavaScript keyboard checks use reduced motion; normal-motion animation checks run separately.

## Live verification

CloudFront invalidation `I4JC0YXE99PTFQYC6KWK4A6LGM` completed. `node deploy/check-dns.mjs`, `python3 deploy/aws_site.py verify --target live`, and `npm run test:live` passed against the published artifact. The live browser exercises all three new landmark buttons and the four-case comparison in addition to the existing reveal, reset, cycle, and geometry controls.

Ordinary IPv4/IPv6 DNS resolves. Valid HTTPS serves the exact reviewed bytes at `/`, `/index.html`, and the tested group query. HTTP redirects the essay, query URLs, and `robots.txt` to HTTPS. Direct S3 access to both public CloudFront objects returns 403. The page makes no additional runtime asset requests and reports no browser errors.

The non-secret resource state and verification receipts are in `deploy/hosting.json` and `deploy/live-verification.json`. The release manifest is [releases/v1.0.5/manifest.json](releases/v1.0.5/manifest.json).

## Outstanding evidence

Fresh-reader feedback remains pending; see [READER-CHECK.md](READER-CHECK.md). Automated and AI review do not substitute for human comprehension evidence. The broader repository CI has its previously recorded generated-documentation and Yarn/Corepack issues; the dedicated essay workflow is this publication's release gate.
