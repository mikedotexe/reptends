import {
  MAX_RANGE, MAX_CHECK_POSITION, parseWhole, digitWindow, formatDigit, checkByLongDivision,
} from "./math/digit-index.ts";

type Found = ReturnType<typeof digitWindow>;
type FieldName = "a" | "d" | "b" | "from" | "to";
type Fields = Record<FieldName, string>;
const names: readonly FieldName[] = ["a", "d", "b", "from", "to"];
const defaults: Fields = { a: "1", d: "997", b: "10", from: "1", to: "60" };
const presets: Record<string, Fields> = {
  start: defaults,
  far: { a: "1", d: "7", b: "10", from: "1000000000", to: "" },
  return: { a: "1", d: "997", b: "1000", from: "167", to: "" },
  huge: { a: "1", d: "9899", b: "10", from: "10^100", to: "" },
  improper: { a: "22", d: "7", b: "10", from: "1", to: "30" },
};

function compact(value: bigint): string {
  const text = value.toString();
  if (text.length <= 18) return text;
  if (/^10+$/.test(text)) return "10^" + (text.length - 1);
  return `${text.slice(0, 8)}…${text.slice(-6)} (${text.length} digits)`;
}

/** The public inputs and URL use one-based positions in the selected radix. */
export function initDigitIndexExplorer(): void {
  const get = <T extends HTMLElement>(id: string): T => {
    const found = document.getElementById(id);
    if (!found) throw new Error("Missing indexed-digit element: " + id);
    return found as T;
  };
  const put = (id: string, value: string | bigint) => { get(id).textContent = String(value); };
  const inputs: Record<FieldName, HTMLInputElement> = {
    a: get("di-numerator"), d: get("di-denominator"), b: get("di-radix"),
    from: get("di-from"), to: get("di-to"),
  };
  let current: Found | null = null;
  let dirty = false;
  let controller: AbortController | null = null;
  let walked = 0n;
  let revision = 0;

  function fill(fields: Fields): void {
    for (const name of names) inputs[name].value = fields[name];
  }

  function fromURL(): { fields: Fields; invalid: boolean } {
    if (window.location.search.length > 5000) return { fields: defaults, invalid: true };
    const params = new URLSearchParams(window.location.search);
    if (!names.some(name => params.has("di_" + name))) return { fields: defaults, invalid: false };
    const fields = { ...defaults };
    for (const name of names) {
      const entries = params.getAll("di_" + name);
      if (entries.length !== 1 || entries[0]!.length > 1024) return { fields: defaults, invalid: true };
      fields[name] = entries[0]!;
    }
    return { fields, invalid: false };
  }

  function readForm(): Found {
    const numerator = parseWhole(inputs.a.value, "The numerator", 128);
    const denominator = parseWhole(inputs.d.value, "The denominator", 128);
    const radix = parseWhole(inputs.b.value, "The base", 128);
    const start = parseWhole(inputs.from.value, "The first position", 256);
    const end = inputs.to.value.trim() === "" ? start : parseWhole(inputs.to.value, "The last position", 256);
    if (end < start) throw new RangeError("The last position must be at or after the first.");
    const count = end - start + 1n;
    if (count > BigInt(MAX_RANGE)) throw new RangeError(`Choose at most ${MAX_RANGE} positions at a time.`);
    return digitWindow({ numerator, denominator, radix, start, count: Number(count) });
  }

  function resultURL(found: Found, publicURL = false): URL {
    const url = publicURL ? new URL("https://reptends.mikedotexe.com/" + window.location.search) : new URL(window.location.href);
    const values: Fields = {
      a: String(found.numerator), d: String(found.denominator), b: String(found.radix),
      from: String(found.start), to: found.count === 1 ? "" : String(found.start + BigInt(found.count) - 1n),
    };
    for (const name of names) url.searchParams.set("di_" + name, values[name]);
    url.hash = "digit-index";
    return url;
  }

  function remember(found: Found): void {
    if (!/^https?:$/.test(window.location.protocol)) return;
    const url = resultURL(found);
    if (url.href === window.location.href) return;
    try { history.pushState(null, "", url); } catch { /* Embedded and offline copies still calculate. */ }
  }

  function stopCheck(message = ""): void {
    controller?.abort();
    controller = null;
    get("di-check-stop").hidden = true;
    get("di-progress").hidden = true;
    get<HTMLButtonElement>("di-check-start").disabled = dirty || !current || current.start + BigInt(current.count) - 1n > MAX_CHECK_POSITION;
    if (message) put("di-check-status", message);
  }

  function renderPowerBridge(found: Found): void {
    const exponent = found.start - 1n;
    const show = found.numerator === 1n && found.denominator === 997n && found.radix === 1000n && exponent <= 512n;
    get("di-power-bridge").hidden = !show;
    if (!show) return;
    const power = 3n ** exponent;
    const quotient = power / 997n;
    const incoming = 3n * power / 997n;
    const printed = formatDigit(found.digits[0]!, 1000n);
    put("di-power-explanation", `Group ${found.start} corresponds to 3^${exponent}. Its full value keeps growing; the entering remainder is ${found.remainderBefore}, and the ordinary group is ${printed}.`);
    put("di-full-power", `3^${exponent} = ${power}`);
    put("di-power-quotient", quotient);
    put("di-power-carry", incoming);
    put("di-power-equation", `${power} + ${incoming} − 1000 × ${quotient} = ${found.digits[0]}`);
  }

  function render(found: Found): void {
    const end = found.start + BigInt(found.count) - 1n;
    const prefix = found.count === 1 ? `Position ${compact(found.start)}` : `Positions ${compact(found.start)}–${compact(end)}`;
    put("di-result-title", `${prefix} of ${compact(found.numerator)}/${compact(found.denominator)}`);
    const baseDescription = found.radix === 1000n ? "three-digit groups" : found.radix <= 36n ? "ordinary digits" : "bracketed digit values";
    put("di-result-base", `Base ${compact(found.radix)} · ${baseDescription}`);
    const separator = found.radix <= 36n ? "" : " ";
    const text = found.digits.map(d => formatDigit(d, found.radix)).join(separator);
    const tape = get("di-tape");
    tape.textContent = text;
    tape.dataset.single = String(found.count === 1);
    tape.setAttribute("aria-label", `Base ${found.radix} digits at positions ${found.start} through ${end}`);
    tape.setAttribute("tabindex", "0");
    tape.scrollTop = 0;
    let note = found.radix === 1000n
      ? "Each group is one base-1000 digit, written with three decimal characters. Its position is not an individual decimal-place number."
      : found.radix <= 36n && found.radix > 10n
        ? "Digit symbols use 0–9, then A–Z. Positions count digits in the selected base."
        : found.radix > 36n
          ? "Each bracket contains one digit value written in decimal. Positions count whole brackets."
          : "Positions count digits after the point in the selected base.";
    note += ` The whole-number part is ${compact(found.integerPart)}.`;
    if (found.numerator % found.denominator === 0n) note += " This fraction is a whole number, so every fractional digit is zero.";
    else if (found.remainderBefore === 0n) note += " The expansion has already terminated; these positions are zero.";
    else if (found.remainderAfter === 0n) note += " The remaining digits after this range are zero.";
    if ([found.numerator, found.denominator, found.radix, found.start, end].some(value => value.toString().length > 18 && !/^10+$/.test(value.toString()))) {
      note += " Long values in the heading are abbreviated; the formula and copied link retain the exact values.";
    }
    put("di-result-note", note);
    const reduced = found.numerator % found.denominator;
    put("di-remainder-label", `Entering remainder at position ${compact(found.start)}`);
    put("di-remainder-equation", `(${reduced} × ${found.radix}^(${found.start} − 1)) mod ${found.denominator} = ${found.remainderBefore}`);
    put("di-digit-label", `Digit at position ${compact(found.start)}`);
    put("di-digit-equation", `⌊${found.radix} × ${found.remainderBefore} / ${found.denominator}⌋ = ${found.digits[0]}${found.radix > 10n ? ` (displayed ${formatDigit(found.digits[0]!, found.radix)})` : ""}`);
    get("di-error").hidden = true;
    get("di-copy-field-label").hidden = true;
    put("di-copy-status", "");
    put("di-copy", "Copy digits");
    put("di-share", "Copy a link to this result");
    put("di-check-status", "");
    const canCheck = end <= MAX_CHECK_POSITION;
    get<HTMLButtonElement>("di-check-start").disabled = !canCheck;
    put("di-check-help", canCheck
      ? `Walk from the beginning through position ${end}, then compare the entering remainder and ${found.count === 1 ? "requested digit" : `all ${found.count} requested digits`}.`
      : `The direct result is available. This page limits a sequential check to position ${MAX_CHECK_POSITION}; walking to ${compact(end)} is outside that practical limit.`);
    renderPowerBridge(found);
  }

  function find(updateURL: boolean): boolean {
    revision++;
    stopCheck();
    try {
      const found = readForm();
      current = found;
      dirty = false;
      render(found);
      if (updateURL) remember(found);
      return true;
    } catch (error) {
      dirty = true;
      get<HTMLButtonElement>("di-check-start").disabled = true;
      put("di-error", error instanceof Error ? error.message : "The inputs could not be read.");
      get("di-error").hidden = false;
      put("di-check-status", "The result above still belongs to the last valid search. Correct the inputs and choose Find digits.");
      return false;
    }
  }

  async function copyText(text: string, message: string): Promise<void> {
    const resultRevision = revision;
    try {
      if (!navigator.clipboard?.writeText) throw new Error("Clipboard unavailable");
      await navigator.clipboard.writeText(text);
      if (revision === resultRevision) put("di-copy-status", message);
    } catch {
      if (revision !== resultRevision) return;
      const field = get<HTMLTextAreaElement>("di-copy-field");
      field.value = text;
      get("di-copy-field-label").hidden = false;
      put("di-copy-status", "Select and copy the text below.");
      field.focus({ preventScroll: true });
      field.select();
    }
  }

  get<HTMLFormElement>("di-form").addEventListener("submit", event => { event.preventDefault(); find(true); });
  for (const input of Object.values(inputs)) input.addEventListener("input", () => {
    dirty = true;
    revision++;
    stopCheck("Inputs changed. Choose Find digits to update the result.");
    get("di-copy-field-label").hidden = true;
    put("di-copy-status", "");
  });
  document.querySelectorAll<HTMLButtonElement>("[data-di-preset]").forEach(button => {
    button.addEventListener("click", () => {
      const preset = presets[button.dataset.diPreset!];
      if (preset) { fill(preset); find(true); }
    });
  });
  get("di-copy").addEventListener("click", () => {
    if (current) void copyText(current.digits.map(d => formatDigit(d, current!.radix)).join(current.radix <= 36n ? "" : " "), "Digits copied.");
  });
  get("di-share").addEventListener("click", () => {
    if (current) void copyText(resultURL(current, true).href, "Result link copied.");
  });
  get("di-check-stop").addEventListener("click", () => stopCheck(`Stopped after ${walked} positions. The direct result remains available.`));
  get("di-check-start").addEventListener("click", async () => {
    if (!current || dirty || current.start + BigInt(current.count) - 1n > MAX_CHECK_POSITION) return;
    stopCheck();
    const found = current;
    const mine = new AbortController();
    controller = mine;
    walked = 0n;
    const end = found.start + BigInt(found.count) - 1n;
    get<HTMLButtonElement>("di-check-start").disabled = true;
    get("di-check-stop").hidden = false;
    const progress = get<HTMLProgressElement>("di-progress");
    progress.value = 0;
    progress.hidden = false;
    put("di-check-status", "Starting at the first fractional position.");
    try {
      const result = await checkByLongDivision(found, {
        signal: mine.signal,
        onProgress: completed => {
          if (controller !== mine) return;
          walked = completed;
          progress.value = Number(completed * 100n / end);
          put("di-check-status", `Checked ${completed} of ${end} positions.`);
        },
      });
      if (controller !== mine) return;
      walked = result.steps;
      stopCheck();
      put("di-check-status", result.status === "matched"
        ? `Confirmed. Sequential long division agrees on the entering remainder and all ${found.count} requested digit${found.count === 1 ? "" : "s"}.`
        : result.status === "cancelled"
          ? `Stopped after ${result.steps} positions.`
          : `The independent check found a mismatch${result.mismatchPosition === undefined ? "" : ` at position ${result.mismatchPosition}`}.`);
    } catch (error) {
      if (controller !== mine) return;
      stopCheck();
      put("di-check-status", error instanceof Error ? error.message : "The sequential check could not complete.");
    }
  });
  function restoreURL(): void {
    const restored = fromURL();
    fill(restored.fields);
    const valid = find(false);
    if (!valid) { fill(defaults); find(false); }
    if (restored.invalid || !valid) {
      put("di-error", "The linked inputs were invalid or too large. Showing the first 60 decimal digits of 1/997.");
      get("di-error").hidden = false;
    }
  }
  window.addEventListener("popstate", restoreURL);
  restoreURL();
}
