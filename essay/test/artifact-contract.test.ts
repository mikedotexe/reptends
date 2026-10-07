import test from "node:test";
import assert from "node:assert/strict";
import { assertPublishableHtml } from "../scripts/validate-artifact.ts";

test("publishing rejects synthetic credentials without echoing them", () => {
  const fixtures = [
    `<!-- ${"AKIA" + "A".repeat(16)} -->`,
    `<script>const key = '${"ASIA" + "B".repeat(16)}';</script>`,
    `aws_secret_access_key = ${"c".repeat(40)}`,
    `{"secretAccessKey":"${"D".repeat(40)}"}`,
    "Access key ID,Secret access key",
    "-----BEGIN PRIVATE KEY-----",
  ];
  for (const fixture of fixtures) {
    assert.throws(() => assertPublishableHtml(fixture, ""), error => {
      assert(error instanceof Error);
      assert.match(error.message, /credential pattern/);
      assert(!error.message.includes(fixture));
      return true;
    });
  }
});

test("publishing permits reference links and inline diagrams but refuses asset requests", () => {
  assert.doesNotThrow(() => assertPublishableHtml(
    '<a href="https://example.org/paper">Reference</a><svg><use href="#diagram"/></svg><script>const exact = 997n;</script>',
    ':root { color: #123; } .mark { background-image: url("data:image/svg+xml;base64,AAAA"); }',
  ));
  for (const fixture of [
    '<script src="bundle.js"></script>',
    '<link rel="stylesheet" href="https://example.org/theme.css">',
    '<img src="plot.png" alt="Plot">',
    '<source srcset="image.png 1x, large.png 2x">',
    '<iframe src="https://example.org"></iframe>',
  ]) {
    assert.throws(() => assertPublishableHtml(fixture, ""), /external asset/);
  }
  for (const fixture of [
    '@import "https://example.org/theme.css";',
    '.hero { background: url(https://example.org/image.png); }',
    '@font-face { src: url("fonts/serif.woff2"); }',
  ]) {
    assert.throws(() => assertPublishableHtml("", fixture), /external asset/);
  }
});
