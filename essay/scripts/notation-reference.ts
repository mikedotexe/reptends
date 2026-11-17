import { progressionExamples, progressionInfo, progressionRows } from "../src/math/progression.ts";
import { progressionRuns, runDigits } from "../src/math/run-notation.ts";

const atlas = "https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md";
export function notationCertificate() {
  return {
    schema_version:1, kind:"mixed-radix-run-notation", integer_encoding:"decimal strings",
    notation_status:"implemented-here: display convention; underlying arithmetic reproved-here in Lean",
    grammar:{run:"⟨d1, d2, ..., dL⟩_B", comma:"successive digit positions", subscript:"radix used L times", bar:"radix change, not necessarily a remainder return", initial_point:"fractional expansion starts here", counting_ellipsis:"all integers between the displayed endpoints", final_ellipsis:"continue the specified generator using the balance policy"},
    semantics:{digit_domain:"integer B >= 2; integer 0 <= d < B", initial_state:{P:"1",Q:"0",r:"A"}, digit_update:"P' = P*B; Q' = B*Q+d; r' = B*r-D*d", invariant:"D*Q+r=A*P", exact_value:"A/D = Q/P+r/(D*P)", run_value:"pack_B(d1,...,dL)/(P_before*B^L)", digit_weight:"1 / product of all radices through this digit (including repeated uses inside a run)", printed_integer_base:"decimal for readability; independent of each mathematical radix"},
    policy:{preconditions:"D > r > 0, B >= 2, next supplied term a >= 0",trial:"T=B*r-D*a",keep:"0<=T<D",finish:"T=0: stop or pad with zero digits",change:"if T<0 or T>=D and a>0, use R=floor(D*a/r)+1; next remainder R*r-D*a",zero_target:"An accepted zero is allowed; a rejected zero requires a separate feasibility analysis.",completed:"r=0 emits only zero digits in every subsequent radix."},
    claims:[
      {id:"mixed_radix_run_value_preservation",url:atlas+"#mixed_radix_run_value_preservation",module:"lean/RadixRuns/Encoding.lean",theorems:["RadixRuns.Run.packed_eq_horner","RadixRuns.Run.digitValue_eq_packed"]},
      {id:"mixed_radix_run_value_preservation",url:atlas+"#mixed_radix_run_value_preservation",module:"lean/RadixRuns/Core.lean",theorems:["RadixRuns.DivisionState.advance_prefix_value","RadixRuns.DivisionState.advance_value","RadixRuns.DivisionState.radix_change_preserves_value"]},
      {id:"unified_balance_rule",url:atlas+"#unified_balance_rule",module:"lean/RadixRuns/BalanceRule.lean",theorems:["RadixBalance.chosen_digit_legal","RadixBalance.chosen_preserves_prefix","RadixBalance.zero_finishes","RadixBalance.completed_stays_completed","RadixBalance.after_prefix_hasSum"]}
    ],
    limitations:["The supplied progression is not uniquely selected by the fraction.","Changing radices changes weights; ordinary positional notation retains the exact value.","Lean proves the mathematics, not the glyphs, JSON, or browser implementation.","The stream theorem uses positive targets after any separately certified initial zero prefix."],
    examples:progressionExamples.map(example => {
      const info=progressionInfo(example), runs=progressionRuns(example,8), rows=progressionRows(example,8);
      return {id:example,numerator:"1",denominator:String(info.denominator),initial_radix:String(info.originalRadix),
        generator:example==="powers"?{seeds:["1"],recurrence:"a(n+1)=3*a(n)"}:example==="fibonacci"?{seeds:["0","1"],recurrence:"a(n+2)=a(n+1)+a(n)"}:{seeds:["0"],recurrence:"a(n+1)=a(n)+1"},
        runs:runs.map(run=>({radix:String(run.radix),length:run.digits.length,digits:run.digits.map(String)})),
        steps:rows.map(row=>({position:row.position,digit:String(row.desired),current_radix:String(row.currentRadix),trial:String(row.candidate),action:row.action,radix:String(row.radix),remainder_before:String(row.before.remainder),remainder_after:String(row.after.remainder)}))};
    })
  };
}

export function renderNotationCertificate(): string {
  return `<script type="application/json" id="reptends-notation">${JSON.stringify(notationCertificate()).replace(/</g,"\\u003c")}</script>`;
}

export function renderNotationExamples(): string {
  return `<details id="notation-examples" class="math-note"><summary>Read all three examples together</summary>${progressionExamples.map(example=>{
    const info=progressionInfo(example), runs=progressionRuns(example);
    return `<article class="notation-example" data-example="${example}"><h3>1/${info.denominator} · ${info.patternLabel}</h3><p class="notation-static" role="math" aria-label="Fraction one over ${info.denominator}; runs in order, each with its radix"><span>0.</span>${runs.map((run,i)=>`<span class="hp-changed-run">${i?'<span aria-label="change radix">|</span>':''}<span class="notation-run"><span>${runDigits(run,true)}</span><sub>${run.radix}</sub></span></span>`).join("")}<span>| …</span></p>${example==='counting'?'<p class="fine-print">The first run contains every integer from 0 through 997: 998 successive digits.</p>':''}</article>`;
  }).join("")}</details>`;
}
