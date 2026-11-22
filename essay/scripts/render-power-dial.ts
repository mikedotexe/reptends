import { renderPowerFamily, renderRegrouping } from "../src/power-dial-view.ts";

export function renderPowerDialChapter(): string {
  return `<section id="power-and-grouping" class="chapter power-chapter wrap" aria-labelledby="power-chapter-title" tabindex="-1">
    <div class="chapter-heading"><span class="chapter-number">08 / CHANGE ONE THING AT A TIME</span><h2 id="power-chapter-title">Give the pattern<br>more room.</h2></div>
    <div class="prose"><p>There are two experiments to try. We can move to a new fraction with the same gap below a power of ten. Or we can keep 1/997 and read its digits in wider groups. Each control below changes just one of those choices.</p></div>
    <article id="power-family" class="power-workbench" aria-labelledby="power-family-title">
      <p class="dial-label">Experiment A · a family of fractions</p><h3 id="power-family-title">Keep the gap at 3.<br>Raise the power.</h3>
      <p>97, 997, 9997, … each sit three below a power of ten. Each reciprocal starts from the same series coefficients: <strong>1, 3, 9, 27, …</strong>. Larger boxes let more of that progression appear before a carry changes a group.</p>
      <div class="power-dial-controls enhancement">
        <label for="power-width">Power of ten <output id="power-width-label" for="power-width">10³ · 3-digit boxes</output></label>
        <input id="power-width" type="range" min="2" max="6" step="1" value="3">
        <div class="dial-presets" role="group" aria-label="Choose a power of ten">${[2,3,4,5,6].map(w => `<button type="button" data-power-width="${w}" aria-label="10 to the power ${w}">10<sup>${w}</sup></button>`).join("")}</div>
      </div>
      <div id="power-result">${renderPowerFamily(3)}</div>
      <p id="power-status" class="sr-only" aria-live="polite" aria-atomic="true"></p>
    </article>
    <p class="chapter-bridge">The first dial changed the denominator along with the size of a box. Now return to 997 and hold the fraction still.</p>
    <article id="fixed-997-grouping" class="power-workbench" aria-labelledby="fixed-grouping-title">
      <p class="dial-label">Experiment B · one fraction</p><h3 id="fixed-grouping-title">Keep 997.<br>Move the group boundaries.</h3>
      <p>The digits below always belong to <strong>1/997</strong>. Try three-digit boxes, then six-digit boxes. Pairing two groups changes the visible multiplier from 3 to 9 and the first coefficient from 1 to 1003.</p>
      <div class="power-dial-controls enhancement">
        <label for="group-width">Digits in each box <output id="group-width-label" for="group-width">3</output></label>
        <input id="group-width" type="range" min="3" max="6" step="1" value="3">
        <div class="dial-presets" role="group" aria-label="Choose the grouping width">${[3,4,5,6].map(w => `<button type="button" data-group-width="${w}">${w} digits</button>`).join("")}</div>
      </div>
      <div id="group-result">${renderRegrouping(3)}</div>
      <p class="group-takeaway">Wider groups can expose a different progression. They do not guarantee more unchanged opening groups: the division’s remainder decides that.</p>
      <p id="group-status" class="sr-only" aria-live="polite" aria-atomic="true"></p>
    </article>
    <details id="power-dial-proof" class="math-note power-proof"><summary>Check the carry threshold and the one-unit width</summary><div class="prose">
      <p>The <a href="https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md#power-dial-and-fixed-grouping-examples">worked-example record</a> gives this lesson’s scope. The series and carry calculation use the registered positive-quotient identity and incoming-carry formula; the field-width calculation is elementary algebra.</p>
      <p>In the first experiment, B = 10<sup>w</sup> and n = B − 3. Let K be the largest integer with 3<sup>K</sup> &lt; n, so 3<sup>K</sup> &lt; n ≤ 3<sup>K+1</sup>. The first K groups are unchanged. The first changed group has coefficient 3<sup>K</sup> and receives the incoming carry floor(3<sup>K+1</sup>/n). This quotient accounts for the entire later tail, not just the next written row.</p>
      <p>For the field around B, the boundary equation is (B − n)² = n. If its lower square-root boundary is x, then x²+x = B. Its upper boundary is x+1, because (x+1)²−(x+1) = x²+x. The exact root width is therefore 1 for each selected power.</p>
      <p class="formula">Root boundaries: (√(4B+1) − 1)/2 and (√(4B+1) + 1)/2<br>Ordinary width: √(4B+1).</p>
      <p>In the second experiment, write B = q×997 + k with the ordinary remainder 0 &lt; k &lt; 997. The coefficients are <strong>q, qk, qk², …</strong>. They are pure powers starting at 1 only when q = 1. At the first changed group j+1, the incoming carry is floor(k<sup>j+1</sup>/997). The grouping control changes B, q, and k together; the fraction stays 1/997.</p>
    </div></details>
    <details id="power-dial-conclusion" class="math-note power-proof"><summary>How far can we take these two experiments?</summary><div class="prose">
      <p>For any finite number K of powers of three, choose a power B large enough that B − 3 &gt; 3<sup>K</sup>. The first K groups of 1/(B − 3) then show those powers unchanged. To keep the progression visible indefinitely in one fraction, <a href="#change-radix">the earlier changing-radix construction</a> gives later terms larger places and tracks their new weights.</p>
      <p>For fixed 1/997, we can instead group its complete <strong>166-digit decimal period</strong> into one digit in base 10<sup>166</sup>. If that entire block is C, then 10<sup>166</sup> = 997×C + 1: write C and return to remainder 1. This is the <a href="#one-digit">whole-block-as-one-digit idea</a> again. It packages the full period; the block still contains all 166 decimal positions, including its leading zeros. The earlier loop of 166 three-digit groups spans 498 decimal digits: three copies of this decimal period.</p>
    </div></details>
  </section>`;
}
