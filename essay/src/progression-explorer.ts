import { progressionInfo, progressionRows, progressionBefore, progressionExamples, type ProgressionExample } from "./math/progression.ts";
import { decimalTruncation } from "./run-radices.ts";

const stepCount = 8;
const superscript = (n: number) => String(n).replace(/[0-9]/g, d => "⁰¹²³⁴⁵⁶⁷⁸⁹"[Number(d)]!);

export function initProgressionExplorer(): void {
  const examples = { powers: progressionRows("powers", stepCount), fibonacci: progressionRows("fibonacci", stepCount), counting: progressionRows("counting", stepCount) };
  const before = { powers: progressionBefore("powers"), fibonacci: progressionBefore("fibonacci"), counting: progressionBefore("counting") };
  let example: ProgressionExample = "powers";
  let selected = 0;
  const get = <T extends HTMLElement>(id: string): T => {
    const node = document.getElementById(id);
    if (!node) throw new Error("Missing progression explorer element: " + id);
    return node as T;
  };
  const put = (id: string, value: string | bigint) => { get(id).textContent = String(value); };
  const slider = get<HTMLInputElement>("hp-position");
  function restore(): void {
    const query = new URLSearchParams(window.location.search);
    const choices = query.getAll("hp");
    example = choices.length === 1 && progressionExamples.includes(choices[0] as ProgressionExample) ? choices[0] as ProgressionExample : "powers";
    const steps = query.getAll("hp_step");
    selected = steps.length === 1 && /^[0-8]$/.test(steps[0]!) ? Number(steps[0]) - 1 : 0;
  }
  function render(announce = false): void {
    const info = progressionInfo(example);
    const rows = examples[example];
    const first = rows[0]!;
    const row = selected === -1 ? before[example] : rows[selected]!;
    const next = selected === -1 ? first.desired : selected + 1 < rows.length ? rows[selected + 1]!.desired : example === "powers" ? row.desired * 3n : example === "counting" ? row.desired + 1n : row.desired + rows[selected - 1]!.desired;
    get("hp-powers").setAttribute("aria-pressed", String(example === "powers"));
    get("hp-fibonacci").setAttribute("aria-pressed", String(example === "fibonacci"));
    get("hp-counting").setAttribute("aria-pressed", String(example === "counting"));
    put("hp-title", info.patternLabel + ".");
    put("hp-fraction", `1/${info.denominator}`);
    put("hp-origin", info.origin);
    put("hp-prefix", info.prefixLabel);
    put("hp-prefix-note", `${info.prefixLength} digits in radix ${info.originalRadix}; the remainder is ${info.initialRemainder}.${example !== "powers" ? " The initial zero group counts as a digit." : ""}`);
    put("hp-fixed-first", first.ordinaryDigit.toString().padStart(info.originalRadix === 100n ? 2 : 3, "0"));
    put("hp-changed-first", first.desired);
    put("hp-first-radix", first.radix);
    put("hp-original-radix", info.originalRadix);
    put("hp-switch-note", "The comparison above marks the first change. Use the arrows below to inspect the balance before and after it.");
    put("hp-balance", `${row.currentRadix} × ${row.before.remainder} − ${info.denominator} × ${row.desired} = ${row.candidate}`);
    put("hp-decision", row.action === "keep" ? `Keep radix ${row.currentRadix}` : row.action === "finish" ? "Complete" : `Change radix ${row.currentRadix} → ${row.radix}`);
    put("hp-reason", row.action === "finish" ? "The leftover is zero. The written digits equal the fraction exactly." : row.action === "keep" ? `${row.candidate} is positive and smaller than ${info.denominator}. The next term already fits.` : row.candidate < 0n ? "The leftover would be negative. The next term needs a different radix." : `The leftover is at least ${info.denominator}. It would change the printed digit.`);
    put("hp-choice", row.action === "change" ? `New radix = ⌊${info.denominator} × ${row.desired} / ${row.before.remainder}⌋ + 1 = ${row.radix}` : "The current radix passes the balance check.");
    slider.value = String(selected);
    slider.setAttribute("aria-valuetext", `Digit ${selected === -1 ? "before the switch" : `${selected + 1} of ${stepCount}`}: ${row.desired} in radix ${row.radix}, position ${row.position} in this representation.`);
    put("hp-step-label", selected === -1 ? "Before the switch" : `${selected + 1} of ${stepCount}`);
    put("hp-position-note", `Digit position ${row.position} in this representation`);
    put("hp-radix", row.radix);
    put("hp-digit", row.desired);
    get("hp-radix").dataset.exact = String(row.radix);
    get("hp-digit").dataset.exact = String(row.desired);
    put("hp-remainder", `${row.before.remainder} → ${row.after.remainder}`);
    put("hp-equation", `${row.radix} × ${row.before.remainder} = ${info.denominator} × ${row.desired} + ${row.after.remainder}`);
    get<HTMLButtonElement>("hp-previous").disabled = selected === -1;
    get<HTMLButtonElement>("hp-next").disabled = selected === stepCount - 1;
    const start = Math.max(0, Math.min(stepCount - 3, selected - 1));
    get("hp-leading-dots").hidden = start === 0;
    const labels: string[] = [];
    for (let i = 0; i < 3; i++) {
      const token = rows[start + i]!;
      put(`hp-token-digit-${i}`, `[${token.desired}]`);
      put(`hp-token-radix-${i}`, token.radix);
      if (start + i === selected) get(`hp-token-${i}`).setAttribute("aria-current", "step");
      else get(`hp-token-${i}`).removeAttribute("aria-current");
      labels.push(`digit ${token.desired} in radix ${token.radix}`);
    }
    get("hp-inscription").setAttribute("aria-label", `Continuation after the preserved prefix${start ? ", excerpt" : ""}: ${labels.join(", ")}, and so on.`);
    get("hp-observation").setAttribute("aria-live", announce ? "polite" : "off");
    put("hp-observation", `Next comes ${next}. The same balance check decides whether to keep or change the radix.`);
    const oldPlace = `${info.originalRadix}${superscript(info.prefixLength)}`;
    put("hp-first-weights", `${first.desired}/(${oldPlace} × ${first.radix}) + ${rows[1]!.desired}/(${oldPlace} × ${first.radix} × ${rows[1]!.radix}) + …`);
    put("hp-weight-explanation", `The first new digit is ${first.desired}, weighted by 1/(${oldPlace} × ${first.radix}). Every step refines the remaining tail.`);
    put("hp-accounting", `${info.denominator}Q + ${row.after.remainder} = P\nQ/P + ${row.after.remainder}/(${info.denominator}P) = 1/${info.denominator}`);
    get<HTMLTextAreaElement>("hp-place").value = String(row.after.place);
    get<HTMLTextAreaElement>("hp-quotient").value = String(row.after.quotient);
    put("hp-decimal-prefix", `Written prefix, truncated to 20 decimal places: ${decimalTruncation(row.after.quotient,row.after.place)}…`);
    put("hp-share", "Copy a link to this step");
    put("hp-share-help", "Keep this example and position.");
    get("hp-share-label").hidden = true;
  }
  function updateURL(push = false): void {
    if (!/^https?:$/.test(window.location.protocol)) return;
    const url = new URL(window.location.href);
    url.searchParams.set("hp", example);
    url.searchParams.set("hp_step", String(selected + 1));
    try {
      if (push) history.pushState(null, "", url);
      else history.replaceState(null, "", url);
    } catch { /* Restricted previews retain local stepping. */ }
  }
  function select(n: number): void {
    selected = Math.max(-1, Math.min(stepCount - 1, n));
    render(true);
    updateURL();
  }
  for (const choice of progressionExamples) {
    get(`hp-${choice}`).addEventListener("click", () => {
      if (example === choice) return;
      example = choice;
      selected = 0;
      render(true);
      updateURL(true);
    });
  }
  slider.addEventListener("input", () => select(Number(slider.value)));
  get("hp-previous").addEventListener("click", () => select(selected - 1));
  get("hp-next").addEventListener("click", () => select(selected + 1));
  window.addEventListener("popstate", () => { restore(); render(true); });
  get("hp-share").addEventListener("click", async () => {
    const url = new URL("https://reptends.mikedotexe.com/");
    url.searchParams.set("hp", example);
    url.searchParams.set("hp_step", String(selected + 1));
    url.hash = "change-radix";
    try {
      if (!navigator.clipboard?.writeText) throw new Error("Clipboard unavailable");
      await navigator.clipboard.writeText(url.href);
      put("hp-share", "Link copied");
      put("hp-share-help", `Copied a link to 1/${progressionInfo(example).denominator}, ${selected === -1 ? "the step before the switch" : `new digit ${selected + 1}`}.`);
    } catch {
      const field = get<HTMLInputElement>("hp-share-link");
      field.value = url.href;
      get("hp-share-label").hidden = false;
      put("hp-share-help", "Select and copy the link below.");
      field.focus({ preventScroll: true });
      field.select();
    }
  });
  restore();
  render();
}
