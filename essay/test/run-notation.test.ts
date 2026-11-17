import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { evaluateRuns, progressionRuns, runDigits } from "../src/math/run-notation.ts";
import { notationCertificate, renderNotationCertificate } from "../scripts/notation-reference.ts";

test("a run uses its radix per digit, and splitting a run preserves the weighted value", () => {
  for (let B=2n; B<=20n; B++) {
    const digits=[0n,1n,B-1n,1n];
    const whole=evaluateRuns([{radix:B,digits}]);
    assert.equal(whole.place,B**4n);
    assert.equal(whole.quotient,B**2n+(B-1n)*B+1n);
    for (let cut=1;cut<4;cut++) assert.deepEqual(evaluateRuns([
      {radix:B,digits:digits.slice(0,cut)},{radix:B,digits:digits.slice(cut)}]),whole);
  }
  assert.deepEqual(evaluateRuns([{radix:10n,digits:[1n,2n,5n]}]),{place:1000n,quotient:125n});
});

test("every serialized digit in all three examples agrees with independent long division", () => {
  const certificate=notationCertificate();
  assert.deepEqual(certificate.examples.map(e=>[e.denominator,e.runs[0]!.length]),[["997",6],["9899",11],["998001",998]]);
  for(const example of certificate.examples) {
    const D=BigInt(example.denominator);let P=1n,Q=0n,r=1n,position=0;
    for(const [i,run] of example.runs.entries()) {
      const B=BigInt(run.radix);assert.equal(run.length,run.digits.length);
      const before=r;
      for(const text of run.digits) {
        const digit=BigInt(text);assert.equal(digit,B*r/D);
        r=B*r%D;P*=B;Q=B*Q+digit;position++;
        assert.equal(D*Q+r,P);
      }
      if(i>0) {
        const s=example.steps[i-1]!;
        assert.equal(s.position,position);assert.equal(s.radix,run.radix);
        assert.equal(s.remainder_before,String(before));assert.equal(s.remainder_after,String(r));
        assert.equal(BigInt(s.trial),BigInt(s.current_radix)*before-D*BigInt(s.digit));
      }
    }
    assert.deepEqual(evaluateRuns(example.runs.map(run=>({radix:BigInt(run.radix),digits:run.digits.map(BigInt)}))),{place:P,quotient:Q});
    assert.equal(P/D,Q);assert(r>0n);
  }
});

test("first new digit weights retain every radix in the preserved prefix", () => {
  for(const [name,length,B,R,d] of [["powers",6,1000n,998n,729n],["fibonacci",11,100n,99n,89n],["counting",998,1000n,999n,998n]] as const) {
    const runs=progressionRuns(name,1),before=evaluateRuns(runs.slice(0,1)),after=evaluateRuns(runs);
    assert.equal(before.place,B**BigInt(length));assert.equal(after.place,before.place*R);
    assert.equal(after.quotient-before.quotient*R,d);
  }
});

test("run grammar preserves zero positions and rejects illegal digits or ambiguous abbreviation", () => {
  assert.equal(runDigits({radix:100n,digits:[0n,1n,1n]}),"⟨0, 1, 1⟩");
  assert.equal(runDigits(progressionRuns("counting",1)[0]!,true),"⟨0, 1, 2, …, 995, 996, 997⟩");
  for(const run of [{radix:1n,digits:[0n]},{radix:10n,digits:[]},{radix:10n,digits:[-1n]},{radix:10n,digits:[10n]}]) assert.throws(()=>evaluateRuns([run]),RangeError);
  assert.throws(()=>runDigits({radix:100n,digits:Array(13).fill(1n)},true),RangeError);
});

test("embedded notation data is lossless JSON and every proof mapping names an existing theorem", () => {
  const html=renderNotationCertificate();
  const data=JSON.parse(html.slice(html.indexOf('>')+1,html.lastIndexOf('</script>')));
  assert.deepEqual(data,notationCertificate());
  for(const claim of data.claims) {
    const source=readFileSync(new URL('../../'+claim.module,import.meta.url),'utf8');
    for(const theorem of claim.theorems) assert(source.includes('theorem '+theorem.split('.').at(-1)),theorem);
  }
  assert.equal(data.examples[2]!.runs[0]!.digits.length,998);
  assert(data.limitations.some((line:string)=>line.includes('not the glyphs')));
});
