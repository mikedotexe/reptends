import { powerRuns } from "./run-radices.ts";
import { linkToRun, runFromSearch } from "./navigation.ts";

export function initRadixExplorer(): void {
  const rows = powerRuns(997n, 3n, 169);
  let selected = runFromSearch(window.location.search) ?? 3;
  const get = <T extends HTMLElement>(id: string): T => {
    const node = document.getElementById(id);
    if (!node) throw new Error("Missing run explorer element: " + id);
    return node as T;
  };
  const put = (id: string, value: string | bigint) => { get(id).textContent = String(value); };
  const slider = get<HTMLInputElement>("run-position");
  const compact = (value: bigint) => {
    const text = String(value);
    return text.length <= 12 ? text : text.slice(0,6) + "…" + text.slice(-4);
  };
  function render(announce = false): void {
    const row = rows[selected]!;
    const power = "3" + String(selected).replace(/[0-9]/g, d => "⁰¹²³⁴⁵⁶⁷⁸⁹"[Number(d)]!);
    slider.value = String(selected);
    slider.setAttribute("aria-valuetext", `Run ${selected + 1} of 169: ${power}, radix ${row.radix}, digit ${row.packed}, remainder 1 returns.`);
    put("run-position-label", `${selected + 1} of 169`);
    put("run-radix", compact(row.radix));
    put("run-digit", compact(row.packed));
    get("run-radix").dataset.exact = String(row.radix);
    get("run-digit").dataset.exact = String(row.packed);
    put("run-power", power);
    put("run-equation", row.packed.toString().length > 12
      ? `B × 1 = 997 × ${power} + 1`
      : `${row.radix} × 1 = 997 × ${row.packed} + 1`);
    put("run-size-note", row.radix.toString().length > 12
      ? "Long numbers are abbreviated. Open the inspector for every exact digit."
      : "Each emitted digit fits in its radix.");
    get<HTMLButtonElement>("run-previous").disabled = selected === 0;
    get<HTMLButtonElement>("run-next").disabled = selected === 168;
    put("run-state-heading", `After ${selected + 1} runs: P has ${row.after.place.toString().length} digits. The prefix is Q/P; the tail is 1/(997 × P).`);
    get<HTMLTextAreaElement>("run-place").value = String(row.after.place);
    get<HTMLTextAreaElement>("run-quotient").value = String(row.after.quotient);
    put("run-exact-radix", row.radix);
    put("run-exact-digit", row.packed);
    const observation = selected === 168
      ? "The formula continues beyond this demonstration: each next radix and digit grows, and remainder 1 returns."
      : selected >= 165 ? `${power} is still one legal digit. This is a new sequence of place values; its run numbers are separate from the old three-digit groups.`
      : `The next run uses a larger radix and emits ${3n * row.packed}. The remainder will still be 1.`;
    get("run-observation").setAttribute("aria-live", announce ? "polite" : "off");
    put("run-observation", observation);
    put("share-run", "Copy a link to this run");
    put("share-run-help", "Keep this exact step.");
    get("share-run-label").hidden = true;
  }
  function select(n: number): void {
    selected = Math.max(0, Math.min(168, n));
    render(true);
    if (/^https?:$/.test(window.location.protocol)) {
      const url = new URL(window.location.href);
      url.searchParams.set("run", String(selected + 1));
      try { history.replaceState(null, "", url); } catch { /* Restricted previews still support exact stepping. */ }
    }
  }
  slider.addEventListener("input", () => select(Number(slider.value)));
  get("run-previous").addEventListener("click", () => select(selected - 1));
  get("run-next").addEventListener("click", () => select(selected + 1));
  get("run-start").addEventListener("click", () => select(3));
  get("run-166").addEventListener("click", () => select(166));
  window.addEventListener("popstate", () => { selected = runFromSearch(window.location.search) ?? 3; render(true); });
  get("share-run").addEventListener("click", async () => {
    const url = linkToRun(selected);
    try {
      if (!navigator.clipboard?.writeText) throw new Error("Clipboard unavailable");
      await navigator.clipboard.writeText(url);
      put("share-run", "Link copied");
      put("share-run-help", `Copied a link to run ${selected + 1}.`);
    } catch {
      const field = get<HTMLInputElement>("share-run-link");
      field.value = url;
      get("share-run-label").hidden = false;
      put("share-run-help", "Select and copy the link below.");
      field.focus({ preventScroll: true });
      field.select();
    }
  });
  render();
}
