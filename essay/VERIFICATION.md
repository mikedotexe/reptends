# Verification — essay v1.0.4

Published 8 October 2026 (Pacific time). The release has two reviewed public objects:

- `index.html`: 95,171 bytes, SHA-256 `b24198ea5fa6d7308f814450c9d0749f988436b074458991bcac2a3159d38266`
- `robots.txt`: 613 bytes, SHA-256 `5b83e4b5a732add02f74140cfa52abd992278e03ca4685faee545a1ffa771a3b`

The tested source commit is [`bd5ada9`](https://github.com/mikedotexe/reptends/commit/bd5ada9fd4e24cedf70444b7a35d11c7cb54d66c). The later release-record commit does not change either built object.

## Editorial and mathematical result

The essay now begins with the continuous decimal digits of 1/97, 1/997, and 1/9997, marking the clean powers-of-three prefix, its first changed group, and the ensuing “number salad.” It then stays with 1/997: a full-width addition stack shows how overlapping powers produce `729 → 731` and the following groups, and the interactive position control connects the unbounded power, bounded remainder, local base-3 digit, and three-digit decimal word.

The exact synchronized step is displayed as

`3rᵢ = 997dᵢ + rᵢ₊₁`, `1000rᵢ = 997(rᵢ + dᵢ) + rᵢ₊₁`, and `Wᵢ = rᵢ + dᵢ`.

All 332 displayed transitions agree with independent long division. All 333 finite boundaries retain their exact residual accounting. Tests cover `729 → 731`, the next `193` group, the base-3 digit, the return after 166 three-digit groups, and the distinction between a 166-digit minimal decimal period and a 498-place group loop. Square and cube geometry remains available as an optional continuation, including its leading zero groups and separate collection/carrying steps.

## Accessibility and browser verification

Strict TypeScript checking, 46 Node arithmetic/artifact/navigation tests, 13 Python deployment-safety tests, the standalone build, and `git diff --check` passed locally. Full local Chromium 151 and WebKit 26.5 suites passed at mobile, tablet, and desktop widths. They cover keyboard controls, skip and chapter focus, native table semantics, reduced and normal motion, dark mode, JavaScript-disabled reading, exact large-integer states, sharing/history, geometry, and the absence of runtime asset requests or browser errors.

[GitHub Essay browser checks passed](https://github.com/mikedotexe/reptends/actions/runs/37832860611) on Ubuntu 24.04 for Chromium 151.0.7922.34, Firefox 153.0, and WebKit 26.5. Each job independently installed dependencies, checked types, ran the Node and deployment suites, rebuilt the two artifacts, and completed its browser suite.

## Crawler access and publication

The page includes a canonical URL and `index, follow` metadata. The root `robots.txt` explicitly allows current OpenAI, Anthropic, Perplexity, Google, Apple, Meta, Amazon, and Common Crawl tokens, then allows `User-agent: *` for standard search and future standards-respecting agents. It contains no `Disallow` rule.

The private S3 bucket and deployer policy were expanded from one exact key to two exact keys. CloudFront can read only `index.html` and `robots.txt` through the existing Origin Access Control and distribution ARN. The deployer can upload only those two keys and invalidate only that distribution; permission simulations confirm writes elsewhere and deletion of either object remain denied. All four S3 Block Public Access flags remain enabled.

CloudFront invalidation `I4LJIJIWSDG4J2QXTF7AT0PKT3` completed. `node deploy/check-dns.mjs`, `python3 deploy/aws_site.py verify --target live`, and `npm run test:live` passed. Ordinary IPv4/IPv6 DNS resolves; HTTPS serves the exact reviewed bytes and content types at `/`, `/index.html`, and `/robots.txt`; HTTP redirects the essay, query URLs, and `robots.txt` to HTTPS; direct S3 access to both objects returns 403; and the live controls work without console errors or additional asset requests.

Current resource IDs and evidence are in `deploy/hosting.json`, `deploy/live-verification.json`, and the publisher-policy check files. The release manifest is `releases/v1.0.4/manifest.json`.

## Outstanding evidence

Fresh-reader feedback remains pending; the protocol is in [READER-CHECK.md](READER-CHECK.md). Automated or AI checks do not substitute for human comprehension evidence.

The repository's broader legacy CI still reports its established generated-documentation drift and Yarn/Corepack setup-order failures. Lean passes. These failures are outside the essay project; the dedicated essay workflow above is the release gate for this publication.
