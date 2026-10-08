import assert from "node:assert/strict";
import test from "node:test";
import { positionFromSearch, linkToPosition } from "../src/navigation.ts";

test("shared group links round-trip all bounded positions without changing their meaning", () => {
  for (let index = 0; index < 332; index++) {
    const url = new URL(linkToPosition(index));
    assert.equal(url.origin, "https://reptends.mikedotexe.com");
    assert.equal(url.hash, "#repeat");
    assert.equal(positionFromSearch(url.search), index);
  }
});

test("malformed or ambiguous shared positions do not become arithmetic inputs", () => {
  for (const query of ["", "?group=", "?group=0", "?group=-1", "?group=333", "?group=1.5", "?group=1e2", "?group=07", "?group=NaN", "?group=Infinity", "?group=8&group=9", "?group=%3Cscript%3E", "?group=%208", "?group=" + "9".repeat(500)]) {
    assert.equal(positionFromSearch(query), null, query);
  }
  assert.equal(positionFromSearch("?utm_source=friend&group=8"), 7);
  for (const index of [-1, 332, NaN, Infinity, 1.5]) assert.throws(() => linkToPosition(index), RangeError);
});
