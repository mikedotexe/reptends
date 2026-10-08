import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";

const robots = await readFile(new URL("../src/robots.txt", import.meta.url), "utf8");

test("robots.txt welcomes every standards-respecting crawler", () => {
  for (const agent of ["OAI-SearchBot", "GPTBot", "ChatGPT-User", "Claude-SearchBot",
    "ClaudeBot", "Claude-User", "PerplexityBot", "Perplexity-User", "Google-Extended",
    "Applebot-Extended", "meta-webindexer", "meta-externalagent", "meta-externalfetcher",
    "Amazonbot", "Amzn-SearchBot", "Amzn-User", "CCBot"]) {
    assert.match(robots, new RegExp(`^User-agent:\\s*${agent}$`, "m"));
  }
  assert.match(robots, /^User-agent:\s*\*$/m);
  assert.equal(robots.match(/^Allow:\s*\/$/gm)?.length, 2);
  assert.doesNotMatch(robots, /^Disallow:/m);
});
