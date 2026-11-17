import { progressionInfo, progressionRows, type ProgressionExample } from "./math/progression.ts";
import { decimalTruncation } from "./run-radices.ts";

const stepCount = 8;
const superscript = (n: number) => String(n).replace(/[0-9]/g, d => "⁰¹²³⁴⁵⁶⁷⁸⁹"[Number(d)]!);

export function initProgressionExplorer(): void {
  const examples = { powers: progressionRows("powers", stepCount), counting: progressionRows("counting", stepCount) };
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
    example = choices.length === 1 && choices[0] === "counting" ? "counting" : "powers";
    const steps = query.getAll("hp_step");
    selected = steps.length === 1 && /^[1-8]$/.test(steps[0]!) ? Number(steps[0]) - 1 : 0;
  }
  function render(announce = false): void {
    const info = progressionInfo(example);
    const rows = examples[example];
    const first = rows[0]!;
    const row = rows[selected]!;
    const next = example === "powers" ? row.desired * 3n : row.desired + 1n;
    get("hp-powers").setAttribute("aria-pressed", String(example === "powers"));
    get("hp-counting").setAttribute("aria-pressed", String(example === "counting"));
    put("hp-title", info.patternLabel + ".");
    put("hp-fraction", `1/${info.denominator}`);
    put("hp-origin", example === "powers"
      ? "1000 − 997 = 3. Reading in groups of three gives the powers 1, 3, 9, 27… before carrying."
      : "998001 = 999². Reading in groups of three gives the counting terms 0, 1, 2, 3… before carrying.");
    put("hp-prefix", info.prefixLabel);
    put("hp-prefix-note", `${info.prefixLength} digits in radix 1000; the remainder is ${info.initialRemainder}.${example === "counting" ? " The initial 000 counts as a digit." : ""}`);
    put("hp-fixed-first", first.ordinaryDigit.toString().padStart(3, "0"));
    put("hp-changed-first", first.desired);
    put("hp-first-radix", first.radix);
    put("hp-switch-note", example === "powers"
      ? "This first switch keeps remainder 729. Each later step triples the digit and uses a new radix."
      : "This first switch changes the remainder from 997003 to 999. Later steps keep remainder 999 and write the next counting number.");
    slider.value = String(selected);
    slider.setAttribute("aria-valuetext", `New digit ${selected + 1} of ${stepCount}: ${row.desired} in radix ${row.radix}, position ${row.position} in this representation.`);
    put("hp-step-label", `${selected + 1} of ${stepCount}`);
    put("hp-position-note", `Digit position ${row.position} in this representation`);
    put("hp-radix", row.radix);
    put("hp-digit", row.desired);
    get("hp-radix").dataset.exact = String(row.radix);
    get("hp-digit").dataset.exact = String(row.desired);
    put("hp-remainder", `${row.before.remainder} → ${row.after.remainder}`);
    put("hp-equation", `${row.radix} × ${row.before.remainder} = ${info.denominator} × ${row.desired} + ${row.after.remainder}`);
    get<HTMLButtonElement>("hp-previous").disabled = selected === 0;
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
    put("hp-observation", `Next comes ${next}. ${example === "powers" ? "Tripling" : "Counting"} can continue indefinitely as the units change.`);
    const oldPlace = `1000${superscript(info.prefixLength)}`;
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
    selected = Math.max(0, Math.min(stepCount - 1, n));
    render(true);
    updateURL();
  }
  for (const choice of ["powers", "counting"] as const) {
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
      put("hp-share-help", `Copied a link to 1/${progressionInfo(example).denominator}, new digit ${selected + 1}.`);
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
