import { useEffect, useMemo, useRef, useState } from "react";
import SkeletonAnnotatedReptend from "./SkeletonAnnotatedReptend";

// =============================================================================
// Types
// =============================================================================

interface OrbitRow {
  t: number;
  r: number;
  d: number;
  rNext: number;
}

interface OrbitData {
  rows: OrbitRow[];
  digits: number[];
}

interface GoodMode {
  m: number;
  B: number;
  k: number;
  q: number;
  L: number;
  V: number;
  vis: number;
  carryRate: number;
  score: number;
}

interface OverlayData {
  raw: bigint[];
  carried: bigint[];
  carriedDigits: number[];
  mismatches: number;
}

interface OrbitModel {
  b: number;
  m: number;
  Bbig: bigint;
  Bnum: number | null;
  safeB: boolean;
  n: number;
  a: number;
  M: number;
  removed: Map<number, number>;
  basePrimes: number[];
  gcdBM: bigint;
  error: string | null;
  note?: string;
  L: number;
  k?: number;
  q?: number;
  orbit1?: OrbitData;
  orbitA?: OrbitData;
  full1?: OrbitData;
  fullA?: OrbitData;
  R?: bigint;
  goodModes?: GoodMode[];
  overlay?: OverlayData | null;
}

// =============================================================================
// BigInt-safe utilities
// =============================================================================

function gcdBig(a: bigint, b: bigint): bigint {
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  while (b !== 0n) {
    const t = a % b;
    a = b;
    b = t;
  }
  return a;
}

function modPowBig(base: bigint, exp: bigint, mod: bigint): bigint {
  base %= mod;
  let r = 1n;
  let e = exp;
  let b = base;
  while (e > 0n) {
    if (e & 1n) r = (r * b) % mod;
    b = (b * b) % mod;
    e >>= 1n;
  }
  return r;
}

function powBigIntSmall(base: number, exp: number): bigint {
  let r = 1n;
  let b = BigInt(base);
  let e = exp;
  while (e > 0) {
    if (e & 1) r *= b;
    b *= b;
    e >>= 1;
  }
  return r;
}

// =============================================================================
// Number-theoretic utilities
// =============================================================================

function uniquePrimeFactorsNumber(n: number): number[] {
  let x = Math.abs(Math.trunc(n));
  const out: number[] = [];
  if (x < 2) return out;
  if (x % 2 === 0) {
    out.push(2);
    while (x % 2 === 0) x = Math.trunc(x / 2);
  }
  for (let p = 3; p * p <= x; p += 2) {
    if (x % p === 0) {
      out.push(p);
      while (x % p === 0) x = Math.trunc(x / p);
    }
  }
  if (x > 1) out.push(x);
  return out;
}

function factorizeNumber(n: number): Map<number, number> {
  let x = Math.abs(Math.trunc(n));
  const f = new Map<number, number>();
  if (x < 2) return f;
  let c = 0;
  while (x % 2 === 0) {
    x = Math.trunc(x / 2);
    c++;
  }
  if (c) f.set(2, c);
  for (let p = 3; p * p <= x; p += 2) {
    if (x % p === 0) {
      let e = 0;
      while (x % p === 0) {
        x = Math.trunc(x / p);
        e++;
      }
      f.set(p, e);
    }
  }
  if (x > 1) f.set(x, (f.get(x) || 0) + 1);
  return f;
}

function eulerPhiNumber(n: number): number {
  if (n === 0) return 0;
  if (n === 1) return 1;
  const fac = factorizeNumber(n);
  let r = n;
  for (const p of fac.keys()) r = Math.trunc((r / p) * (p - 1));
  return r;
}

function multiplicativeOrderNumber(a: number, mod: number): number | null {
  const aa = ((a % mod) + mod) % mod;
  if (mod === 1) return 1;
  if (gcdBig(BigInt(aa), BigInt(mod)) !== 1n) return null;
  const phi = eulerPhiNumber(mod);
  const phiFac = factorizeNumber(phi);
  let L = phi;

  for (const p of phiFac.keys()) {
    while (L % p === 0) {
      const cand = Math.trunc(L / p);
      const ok = modPowBig(BigInt(aa), BigInt(cand), BigInt(mod)) === 1n;
      if (!ok) break;
      L = cand;
    }
  }

  return L;
}

function stripBaseFactors(n: number, base: number): { M: number; removed: Map<number, number>; basePrimes: number[] } {
  let x = Math.abs(Math.trunc(n));
  const primes = uniquePrimeFactorsNumber(base);
  const removed = new Map<number, number>();
  for (const p of primes) {
    let e = 0;
    while (x % p === 0) {
      x = Math.trunc(x / p);
      e++;
    }
    if (e) removed.set(p, e);
  }
  return { M: x, removed, basePrimes: primes };
}

// =============================================================================
// Display utilities
// =============================================================================

function formatBlock(d: number, width: number): string {
  const s = String(d);
  if (s.length >= width) return s;
  return "0".repeat(width - s.length) + s;
}

function formatBigIntGrouped(x: bigint, group: number = 3): string {
  const s = x.toString();
  const neg = s.startsWith("-");
  const t = neg ? s.slice(1) : s;
  const parts: string[] = [];
  for (let i = t.length; i > 0; i -= group) {
    parts.push(t.slice(Math.max(0, i - group), i));
  }
  const out = parts.reverse().join("_");
  return neg ? "-" + out : out;
}

// =============================================================================
// Analysis utilities
// =============================================================================

function buildOrbitDigits({ a, M, B, L, maxSteps }: { a: number; M: number; B: number; L: number; maxSteps: number }): OrbitData {
  const mod = BigInt(M);
  const BB = BigInt(B);
  let r = BigInt(((a % M) + M) % M);
  const rows: OrbitRow[] = [];
  const digits: number[] = [];

  const steps = Math.min(L, maxSteps);
  for (let t = 0; t < steps; t++) {
    const Br = BB * r;
    const d = Number(Br / mod);
    const rNext = Br % mod;
    rows.push({ t, r: Number(r), d, rNext: Number(rNext) });
    digits.push(d);
    r = rNext;
  }

  return { rows, digits };
}

function scanGoodModes({ b, M, mMax, kMax }: { b: number; M: number; mMax: number; kMax: number }): Array<{ m: number; B: number; k: number; q: number; L: number }> {
  const modes: Array<{ m: number; B: number; k: number; q: number; L: number }> = [];
  const mod = BigInt(M);
  for (let m = 1; m <= mMax; m++) {
    const Bbig = powBigIntSmall(b, m);
    const Bnum = Number(Bbig);
    const safeB = Number.isSafeInteger(Bnum);
    if (!safeB) continue;
    const k = Number(Bbig % mod);
    if (k >= 1 && k <= kMax) {
      const L = multiplicativeOrderNumber(Bnum % M, M);
      if (L != null) {
        const q = (Bnum - k) / M;
        modes.push({ m, B: Bnum, k, q, L });
      }
    }
  }
  return modes;
}

function visibilityLength({ B, k, q, L, cap = 4096 }: { B: number; k: number; q: number; L: number; cap?: number }): number {
  if (k <= 0) return 0;
  if (q <= 0) return 0;
  const BB = BigInt(B);
  const kk = BigInt(k);
  let term = BigInt(q);
  let V = 0;
  const maxI = Math.min(L, cap);
  for (let i = 0; i < maxI; i++) {
    if (term >= BB) break;
    V++;
    term *= kk;
  }
  return V;
}

function normalizeBaseBLeftToRight(raw: bigint[], B: number): bigint[] {
  const out = raw.map((x) => BigInt(x));
  const BB = BigInt(B);
  for (let i = out.length - 1; i > 0; i--) {
    const carry = out[i] / BB;
    out[i] = out[i] % BB;
    out[i - 1] += carry;
  }
  return out;
}

// =============================================================================
// Sub-components
// =============================================================================

interface OrbitCircleProps {
  rows: OrbitRow[];
  blockWidth: number;
  radius?: number;
}

function OrbitCircle({ rows, blockWidth, radius = 160 }: OrbitCircleProps) {
  const N = rows.length;
  const cx = radius + 20;
  const cy = radius + 20;
  const R = radius;
  return (
    <svg width={2 * radius + 40} height={2 * radius + 40} className="w-full max-w-[420px]">
      <circle cx={cx} cy={cy} r={R} fill="none" stroke="currentColor" opacity={0.25} />
      {rows.map((row, i) => {
        const ang = (2 * Math.PI * i) / Math.max(1, N) - Math.PI / 2;
        const x = cx + R * Math.cos(ang);
        const y = cy + R * Math.sin(ang);
        const x2 = cx + (R - 18) * Math.cos(ang);
        const y2 = cy + (R - 18) * Math.sin(ang);
        return (
          <g key={i}>
            <line x1={x2} y1={y2} x2={x} y2={y} stroke="currentColor" opacity={0.25} />
            <circle cx={x} cy={y} r={12} fill="currentColor" opacity={i === 0 ? 0.9 : 0.55} />
            <text
              x={x}
              y={y + 4}
              textAnchor="middle"
              fontSize={10}
              fill="white"
              fontFamily="ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace"
            >
              {formatBlock(row.d, blockWidth)}
            </text>
          </g>
        );
      })}
      <text
        x={cx}
        y={cy}
        textAnchor="middle"
        fontSize={12}
        fill="currentColor"
        opacity={0.8}
        fontFamily="ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace"
      >
        digits on the cycle
      </text>
    </svg>
  );
}

interface ScorePillProps {
  label: string;
  value: string | number;
}

function ScorePill({ label, value }: ScorePillProps) {
  return (
    <div className="inline-flex items-center gap-2 rounded-full border border-stone-200 bg-stone-50 px-3 py-1">
      <span className="text-[11px] font-mono text-stone-600">{label}</span>
      <span className="text-[11px] font-mono text-stone-900">{value}</span>
    </div>
  );
}

// =============================================================================
// Main Component
// =============================================================================

export default function OrbitCoreExplorer() {
  const [base, setBase] = useState(10);
  const [blockWidth, setBlockWidth] = useState(2);
  const [numerator, setNumerator] = useState(1);
  const [denominator, setDenominator] = useState(97);
  const [showRows, setShowRows] = useState(18);
  const [kMax, _setKMax] = useState(5);
  const [mMax, _setMMax] = useState(24);
  void _setKMax; void _setMMax; // Silence unused warnings - could expose as controls later
  const [showOverlay, setShowOverlay] = useState(true); // Start expanded
  const [overlayInline, setOverlayInline] = useState(true); // Inline vs table view

  // TOE moment: animated snap
  const [snapSpeedMs, setSnapSpeedMs] = useState(170);
  const [snapTargetM, setSnapTargetM] = useState<number | null>(null);
  const snapTimer = useRef<ReturnType<typeof setInterval> | null>(null);

  const model = useMemo((): OrbitModel => {
    const b = Math.max(2, Math.trunc(base));
    const m = Math.max(1, Math.trunc(blockWidth));
    const a = Math.trunc(numerator);
    const n = Math.max(1, Math.trunc(denominator));

    const { M, removed, basePrimes } = stripBaseFactors(n, b);
    const Bbig = powBigIntSmall(b, m);

    const Bnum = Number(Bbig);
    const safeB = Number.isSafeInteger(Bnum);

    const info: OrbitModel = {
      b,
      m,
      Bbig,
      Bnum: safeB ? Bnum : null,
      safeB,
      n,
      a,
      M,
      removed,
      basePrimes,
      gcdBM: gcdBig(Bbig, BigInt(M)),
      error: null,
      L: 0,
    };

    if (M === 1) {
      return {
        ...info,
        note: "M=1 after stripping base primes → expansion terminates (no repeating core).",
      };
    }

    if (info.gcdBM !== 1n) {
      return {
        ...info,
        error: `gcd(B, M) ≠ 1 (gcd=${info.gcdBM.toString()}). Try a different block width m or a different base.`,
      };
    }

    if (!safeB) {
      return {
        ...info,
        error: `B=b^m is too large for this demo (b^m exceeds JS safe integer range). Reduce m.`,
      };
    }

    const L = multiplicativeOrderNumber(Bnum % M, M);
    if (L == null) {
      return {
        ...info,
        error: `Could not compute multiplicative order ord_M(B). (Check gcd(B,M)=1)`,
      };
    }

    const k = Number(Bbig % BigInt(M));
    const q = Math.trunc((Bnum - k) / M);

    const orbit1 = buildOrbitDigits({ a: 1, M, B: Bnum, L, maxSteps: Math.max(1, Math.trunc(showRows)) });
    const orbitA = buildOrbitDigits({ a, M, B: Bnum, L, maxSteps: Math.max(1, Math.trunc(showRows)) });

    const full1 = buildOrbitDigits({ a: 1, M, B: Bnum, L, maxSteps: L });
    const fullA = buildOrbitDigits({ a, M, B: Bnum, L, maxSteps: L });

    // R from digits: concatenate base-B digits
    let R = 0n;
    for (const d of full1.digits) R = R * BigInt(Bnum) + BigInt(d);

    const modes = scanGoodModes({ b, M, mMax: Math.max(1, Math.trunc(mMax)), kMax: Math.max(1, Math.trunc(kMax)) });

    // score each mode
    const scored: GoodMode[] = modes.map((r) => {
      const V = visibilityLength({ B: r.B, k: r.k, q: r.q, L: r.L });
      const vis = r.L > 0 ? V / r.L : 0;
      const carryRate = 1 - vis;
      const smallK = 1 / (1 + r.k);
      const score = 0.55 * vis + 0.35 * smallK + 0.10 * (1 - carryRate);
      return { ...r, V, vis, carryRate, score };
    });
    scored.sort((x, y) => y.score - x.score);

    // skeleton overlay for current mode (only meaningful when k < B)
    let overlay: OverlayData | null = null;
    if (k > 0 && k < Bnum && q > 0 && L > 0 && L <= 4096) {
      const raw: bigint[] = [];
      let term = BigInt(q);
      const kk = BigInt(k);
      for (let i = 0; i < L; i++) {
        raw.push(term);
        term *= kk;
      }
      const carried = normalizeBaseBLeftToRight(raw, Bnum);
      const carriedDigits = carried.map((x) => Number(x));
      const mismatches = full1.digits.reduce((acc, d, i) => acc + (d !== carriedDigits[i] ? 1 : 0), 0);
      overlay = {
        raw,
        carried,
        carriedDigits,
        mismatches,
      };
    }

    return {
      ...info,
      L,
      k,
      q,
      orbit1,
      orbitA,
      full1,
      fullA,
      R,
      goodModes: scored,
      overlay,
    };
  }, [base, blockWidth, numerator, denominator, showRows, kMax, mMax]);

  const bestMode = useMemo(() => {
    if (!model.goodModes || model.goodModes.length === 0) return null;
    return model.goodModes[0];
  }, [model.goodModes]);

  const firstGoodMode = useMemo(() => {
    if (!model.goodModes || model.goodModes.length === 0) return null;
    const copy = [...model.goodModes];
    copy.sort((a, b) => a.m - b.m);
    return copy[0];
  }, [model.goodModes]);

  function stopSnap() {
    if (snapTimer.current) {
      clearInterval(snapTimer.current);
      snapTimer.current = null;
    }
    setSnapTargetM(null);
  }

  useEffect(() => {
    if (snapTargetM == null) return;

    if (snapTimer.current) clearInterval(snapTimer.current);

    snapTimer.current = setInterval(() => {
      setBlockWidth((cur) => {
        const c = Math.max(1, Math.trunc(cur));
        if (c === snapTargetM) {
          stopSnap();
          return c;
        }
        if (c < snapTargetM) return c + 1;
        return c - 1;
      });
    }, Math.max(40, Math.trunc(snapSpeedMs)));

    return () => {
      if (snapTimer.current) {
        clearInterval(snapTimer.current);
        snapTimer.current = null;
      }
    };
  }, [snapTargetM, snapSpeedMs]);

  useEffect(() => {
    stopSnap();
  }, [base, denominator]);

  // =============================================================================
  // Render sections
  // =============================================================================

  const header = (
    <div className="flex flex-col gap-2">
      <div className="text-xl sm:text-2xl font-serif font-semibold tracking-tight text-stone-900">Orbit Core Explorer</div>
      <div className="text-sm text-stone-700 max-w-3xl">
        Repeating decimals are a finite orbit in <span className="font-mono">(Z/MZ)×</span> under multiplication by <span className="font-mono">B=b^m</span>.
        In log-coordinates on <span className="font-mono">⟨B⟩</span>, the dynamics is <span className="font-mono">t ↦ t+1</span>—that is,
        stepping through the orbit is just counting. Digits are a deterministic coding.
      </div>
    </div>
  );

  const controls = (
    <div className="grid grid-cols-1 md:grid-cols-2 xl:grid-cols-3 gap-3">
      <div className="rounded-2xl border border-stone-200 bg-white p-4">
        <div className="text-xs font-mono text-stone-500 mb-2">Core inputs</div>
        <div className="grid grid-cols-2 gap-3">
          <label className="text-sm text-stone-700">
            base b
            <input
              className="mt-1 w-full rounded-xl border border-stone-300 px-3 py-2 font-mono"
              type="number"
              value={base}
              min={2}
              onChange={(e) => setBase(parseInt(e.target.value || "10", 10))}
            />
          </label>
          <label className="text-sm text-stone-700">
            block width m
            <input
              className="mt-1 w-full rounded-xl border border-stone-300 px-3 py-2 font-mono"
              type="number"
              value={blockWidth}
              min={1}
              max={15}
              onChange={(e) => setBlockWidth(parseInt(e.target.value || "2", 10))}
            />
          </label>
          <label className="text-sm text-stone-700">
            numerator a
            <input
              className="mt-1 w-full rounded-xl border border-stone-300 px-3 py-2 font-mono"
              type="number"
              value={numerator}
              onChange={(e) => setNumerator(parseInt(e.target.value || "1", 10))}
            />
          </label>
          <label className="text-sm text-stone-700">
            denominator n
            <input
              className="mt-1 w-full rounded-xl border border-stone-300 px-3 py-2 font-mono"
              type="number"
              value={denominator}
              min={1}
              onChange={(e) => setDenominator(parseInt(e.target.value || "97", 10))}
            />
          </label>
        </div>
        <div className="mt-3 grid grid-cols-2 gap-3">
          <label className="text-sm text-stone-700">
            show rows
            <input
              className="mt-1 w-full rounded-xl border border-stone-300 px-3 py-2 font-mono"
              type="number"
              value={showRows}
              min={6}
              max={512}
              onChange={(e) => setShowRows(parseInt(e.target.value || "18", 10))}
            />
          </label>
        </div>
        <div className="mt-3 flex items-center gap-2">
          <input id="overlay" type="checkbox" checked={showOverlay} onChange={(e) => setShowOverlay(e.target.checked)} />
          <label htmlFor="overlay" className="text-sm text-stone-700">
            show skeleton overlay
          </label>
        </div>
      </div>

      <div className="rounded-2xl border border-stone-200 bg-white p-4">
        <div className="text-xs font-mono text-stone-500 mb-2">"Aha" moment: snap to good coordinates</div>
        <div className="text-sm text-stone-700">
          Find a block width <span className="font-mono">m</span> where the residue <span className="font-mono">k = b^m mod M</span> is small—making the pattern visible.
        </div>
        <div className="mt-3 grid grid-cols-2 gap-2">
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm disabled:opacity-50 hover:bg-stone-50"
            disabled={!firstGoodMode}
            onClick={() => {
              if (!firstGoodMode) return;
              setBlockWidth(1);
              setSnapTargetM(firstGoodMode.m);
            }}
          >
            Snap → first good
          </button>
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm disabled:opacity-50 hover:bg-stone-50"
            disabled={!bestMode}
            onClick={() => {
              if (!bestMode) return;
              setBlockWidth(1);
              setSnapTargetM(bestMode.m);
            }}
          >
            Snap → best score
          </button>
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm hover:bg-stone-50"
            onClick={() => stopSnap()}
          >
            stop
          </button>
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm hover:bg-stone-50"
            onClick={() => {
              setBase(10);
              setBlockWidth(1);
              setNumerator(1);
              setDenominator(97);
            }}
          >
            reset 1/97
          </button>
        </div>
        <div className="mt-3 grid grid-cols-2 gap-3">
          <label className="text-sm text-stone-700">
            snap speed (ms)
            <input
              className="mt-1 w-full"
              type="range"
              min={40}
              max={600}
              value={snapSpeedMs}
              onChange={(e) => setSnapSpeedMs(parseInt(e.target.value || "170", 10))}
            />
            <div className="mt-1 font-mono text-xs text-stone-600">{snapSpeedMs}ms</div>
          </label>
          <div className="text-sm text-stone-700">
            <div className="text-xs text-stone-600">current target</div>
            <div className="font-mono">{snapTargetM == null ? "—" : `m=${snapTargetM}`}</div>
            <div className="mt-2 text-xs text-stone-600">try: watch 1/97 jump from chaos (m=1) to powers of 3 (m=2)</div>
          </div>
        </div>
      </div>

      <div className="rounded-2xl border border-stone-200 bg-white p-4">
        <div className="text-xs font-mono text-stone-500 mb-2">Shortcuts</div>
        <div className="grid grid-cols-2 gap-2">
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm hover:bg-stone-50"
            onClick={() => {
              setBase(10);
              setBlockWidth(2);
              setNumerator(1);
              setDenominator(97);
            }}
          >
            1/97 (m=2)
          </button>
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm hover:bg-stone-50"
            onClick={() => {
              setBase(10);
              setBlockWidth(1);
              setNumerator(1);
              setDenominator(7);
            }}
          >
            1/7 (m=1)
          </button>
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm hover:bg-stone-50"
            onClick={() => {
              setBase(10);
              setBlockWidth(2);
              setNumerator(1);
              setDenominator(19);
            }}
          >
            1/19 (m=2)
          </button>
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm hover:bg-stone-50"
            onClick={() => {
              setBase(10);
              setBlockWidth(3);
              setNumerator(1);
              setDenominator(37);
            }}
          >
            1/37 (m=3)
          </button>
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm hover:bg-stone-50"
            onClick={() => {
              setBase(10);
              setBlockWidth(3);
              setNumerator(1);
              setDenominator(996);
            }}
          >
            1/996 (m=3)
          </button>
          <button
            className="rounded-xl border border-stone-300 px-3 py-2 text-sm hover:bg-stone-50"
            onClick={() => {
              setBase(10);
              setBlockWidth(4);
              setNumerator(1);
              setDenominator(9996);
            }}
          >
            1/9996 (m=4)
          </button>
        </div>
        <div className="mt-3 text-xs text-stone-600">
          Tip: set <span className="font-mono">k≤5</span>, then hit Snap.
        </div>
        <div className="mt-2 text-xs text-violet-700 bg-violet-50 rounded-lg p-2">
          <strong>Note:</strong> 1/996 and 1/9996 are composites—the orbit-stack structure is universal.
          Primality adds QR/NQR coset interpretation but doesn't create the pattern.
        </div>
      </div>
    </div>
  );

  const summary = (
    <div className="rounded-2xl border border-stone-200 bg-white p-4">
      <div className="text-xs font-mono text-stone-500 mb-2">Orbit core summary</div>
      <div className="grid grid-cols-1 lg:grid-cols-3 gap-3 text-sm">
        <div className="rounded-xl border border-stone-200 p-3">
          <div className="text-stone-600">Inputs</div>
          <div className="mt-1 font-mono text-stone-900">b={model.b}, m={model.m}</div>
          <div className="font-mono text-stone-900">B=b^m={model.safeB ? model.Bnum : "(big)"}</div>
          <div className="font-mono text-stone-900">a={model.a}, n={model.n}</div>
        </div>
        <div className="rounded-xl border border-stone-200 p-3">
          <div className="text-stone-600">Core modulus</div>
          <div className="mt-1 font-mono text-stone-900">M={model.M}</div>
          <div className="text-xs text-stone-600 mt-1">
            stripped primes of base: <span className="font-mono">{model.basePrimes.join(",") || "(none)"}</span>
          </div>
          <div className="text-xs text-stone-600">
            removed exponents: <span className="font-mono">{Array.from(model.removed.entries()).map(([p, e]) => `${p}^${e}`).join(" ") || "(none)"}</span>
          </div>
        </div>
        <div className="rounded-xl border border-stone-200 p-3">
          <div className="text-stone-600">Subgroup ⟨B⟩</div>
          {model.error ? (
            <div className="mt-2 text-sm text-rose-700">{model.error}</div>
          ) : model.M === 1 ? (
            <div className="mt-2 text-sm text-stone-700">{model.note}</div>
          ) : (
            <>
              <div className="mt-1 flex flex-wrap gap-2">
                <ScorePill label="k" value={model.k ?? 0} />
                <ScorePill label="q" value={model.q ?? 0} />
                <ScorePill label="L" value={model.L} />
                {model.k !== undefined && model.k > 0 && model.safeB && model.Bnum && model.k < model.Bnum ? (
                  <ScorePill
                    label="heuristic vis"
                    value={`${visibilityLength({ B: model.Bnum, k: model.k, q: model.q ?? 0, L: model.L })}/${model.L}`}
                  />
                ) : null}
              </div>
              <div className="mt-2 text-xs text-stone-600">In discrete-log coordinates on ⟨B⟩, the orbit index t is linear (t→t+1).</div>
            </>
          )}
        </div>
      </div>
    </div>
  );

  const goodModes = (
    <div className="rounded-2xl border border-stone-200 bg-white p-4">
      <div className="text-xs font-mono text-stone-500 mb-2">Coordinate audition (ranked)</div>
      {model.error || model.M === 1 ? (
        <div className="text-sm text-stone-700">Pick an n with a repeating core (M&gt;1) and gcd(B,M)=1.</div>
      ) : (
        <div className="overflow-auto">
          <table className="w-full text-sm">
            <thead className="text-left text-stone-600">
              <tr>
                <th className="py-1 pr-3 font-medium">rank</th>
                <th className="py-1 pr-3 font-medium">m</th>
                <th className="py-1 pr-3 font-medium">k</th>
                <th className="py-1 pr-3 font-medium">q</th>
                <th className="py-1 pr-3 font-medium">L</th>
                <th className="py-1 pr-3 font-medium">vis</th>
                <th className="py-1 pr-3 font-medium">score</th>
                <th className="py-1 pr-3 font-medium"></th>
              </tr>
            </thead>
            <tbody>
              {!model.goodModes || model.goodModes.length === 0 ? (
                <tr>
                  <td colSpan={8} className="py-2 text-stone-700">
                    No small-k modes found up to m≤{mMax} with k≤{kMax}. Increase scan range.
                  </td>
                </tr>
              ) : (
                model.goodModes.slice(0, 24).map((r, idx) => (
                  <tr key={`${r.m}-${r.k}`} className="border-t border-stone-100">
                    <td className="py-1 pr-3 font-mono">#{idx + 1}</td>
                    <td className="py-1 pr-3 font-mono">{r.m}</td>
                    <td className="py-1 pr-3 font-mono">{r.k}</td>
                    <td className="py-1 pr-3 font-mono">{r.q}</td>
                    <td className="py-1 pr-3 font-mono">{r.L}</td>
                    <td className="py-1 pr-3 font-mono">{r.V}/{r.L}</td>
                    <td className="py-1 pr-3 font-mono">{r.score.toFixed(3)}</td>
                    <td className="py-1 pr-3">
                      <button
                        className="rounded-lg border border-stone-300 px-2 py-1 text-xs hover:bg-stone-50"
                        onClick={() => setBlockWidth(r.m)}
                      >
                        use m
                      </button>
                    </td>
                  </tr>
                ))
              )}
            </tbody>
          </table>
        </div>
      )}
      <div className="mt-3 text-xs text-stone-600">
        Score is a simple blend of a heuristic visibility fraction and small k. Exact Track 16 observables such as raw-prefix agreement length, incoming-carry position, and stabilization lookahead live in the published atlas and `search-reptends visibility-profiles`.
      </div>
    </div>
  );

  // Build reptend string from digit blocks for inline view
  const reptendString = useMemo(() => {
    if (!model.full1?.digits) return "";
    return model.full1.digits.map(d => formatBlock(d, model.m)).join("");
  }, [model.full1?.digits, model.m]);

  const skeletonOverlay = (
    <div className="rounded-2xl border border-stone-200 bg-white p-4">
      <div className="flex justify-between items-center mb-2">
        <div className="text-xs font-mono text-stone-500">Skeleton overlay (one orbit window)</div>
        {model.overlay && (
          <div className="flex gap-1 text-[10px]">
            <button
              onClick={() => setOverlayInline(true)}
              className={`px-2 py-0.5 rounded ${overlayInline ? 'bg-stone-700 text-white' : 'bg-stone-200 text-stone-600 hover:bg-stone-300'}`}
            >
              Inline
            </button>
            <button
              onClick={() => setOverlayInline(false)}
              className={`px-2 py-0.5 rounded ${!overlayInline ? 'bg-stone-700 text-white' : 'bg-stone-200 text-stone-600 hover:bg-stone-300'}`}
            >
              Table
            </button>
          </div>
        )}
      </div>
      {model.error || model.M === 1 ? (
        <div className="text-sm text-stone-700">No repeating orbit to overlay.</div>
      ) : !model.overlay ? (
        <div className="text-sm text-stone-700">
          Overlay is shown only when <span className="font-mono">0 &lt; k &lt; B</span> and <span className="font-mono">L</span> is small enough.
        </div>
      ) : overlayInline ? (
        /* Inline view using SkeletonAnnotatedReptend */
        <>
          <div className="text-sm text-stone-700 mb-3">
            The skeleton k<sup>j</sup> blocks live directly in the reptend digits.
            {model.k === 1 && (
              <span className="ml-2 text-emerald-600 font-medium">Perfect: k=1 means constant skeleton!</span>
            )}
          </div>
          {reptendString && model.k !== undefined && model.q !== undefined && (
            <SkeletonAnnotatedReptend
              reptend={reptendString}
              m={model.m}
              k={model.k}
              q={model.q}
              maxBlocks={Math.min(12, model.L)}
            />
          )}
        </>
      ) : (
        /* Table view - the original detailed comparison */
        <>
          <div className="text-sm text-stone-700">
            Raw skeleton terms are <span className="font-mono">q·k^t</span> (not digits). Normalize them in base <span className="font-mono">B</span> with carries (right→left) and compare to true digits from the orbit machine.
          </div>
          <div className="mt-3 flex flex-wrap gap-2">
            <ScorePill label="mismatches" value={`${model.overlay.mismatches}/${model.L}`} />
            <ScorePill label="interpretation" value="good coords ≈ low carry pressure" />
          </div>
          <div className="mt-3 overflow-auto">
            <table className="w-full text-sm">
              <thead className="text-left text-stone-600">
                <tr>
                  <th className="py-1 pr-3 font-medium">t</th>
                  <th className="py-1 pr-3 font-medium">raw q·k^t</th>
                  <th className="py-1 pr-3 font-medium">carried digit</th>
                  <th className="py-1 pr-3 font-medium">true digit</th>
                </tr>
              </thead>
              <tbody>
                {model.full1?.digits.slice(0, Math.min(28, model.L)).map((d, i) => {
                  const carried = model.overlay!.carriedDigits[i];
                  const ok = carried === d;
                  return (
                    <tr key={i} className="border-t border-stone-100">
                      <td className="py-1 pr-3 font-mono">{i}</td>
                      <td className="py-1 pr-3 font-mono">{formatBigIntGrouped(model.overlay!.raw[i])}</td>
                      <td className={`py-1 pr-3 font-mono ${ok ? "text-emerald-700" : "text-rose-700"}`}>{formatBlock(carried, model.m)}</td>
                      <td className="py-1 pr-3 font-mono">{formatBlock(d, model.m)}</td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
        </>
      )}
    </div>
  );

  const orbitPanels = (
    <div className="flex flex-col gap-4">
      <div className="rounded-2xl border border-stone-200 bg-white p-4">
        <div className="flex items-start justify-between gap-3">
          <div>
            <div className="text-xs font-mono text-stone-500">Orbit (1/M) in base B</div>
            {!model.error && model.M !== 1 && (
              <div className="mt-1 text-sm text-stone-700">
                digits are a coding of r → (B·r mod M), length L={model.L}
              </div>
            )}
          </div>
          {!model.error && model.M !== 1 && model.full1 && model.R !== undefined ? (
            <div className="text-right min-w-0">
              <div className="text-xs text-stone-600">repetend integer R</div>
              <div className="font-mono text-stone-900 text-sm break-all">{formatBigIntGrouped(model.R)}</div>
            </div>
          ) : null}
        </div>

        {model.error || model.M === 1 ? (
          <div className="mt-3 text-sm text-stone-700">No repeating orbit to display.</div>
        ) : (
          <>
            <div className="mt-4 flex flex-col lg:flex-row gap-4 items-start">
              {model.orbit1 && <OrbitCircle rows={model.orbit1.rows} blockWidth={model.m} />}
              <div className="flex-1 w-full">
                <div className="text-xs text-stone-600">
                  The orbit visits each remainder exactly once before returning. In discrete-log coordinates, stepping is linear (t → t+1).
                </div>
              </div>
            </div>

            <div className="mt-4 overflow-auto">
              <table className="w-full text-sm">
                <thead className="text-left text-stone-600">
                  <tr>
                    <th className="py-1 pr-3 font-medium">t</th>
                    <th className="py-1 pr-3 font-medium">r_t</th>
                    <th className="py-1 pr-3 font-medium">digit d_t = ⌊B r_t / M⌋</th>
                    <th className="py-1 pr-3 font-medium">r_{"t+1"}</th>
                  </tr>
                </thead>
                <tbody>
                  {model.orbit1?.rows.map((row) => (
                    <tr key={row.t} className="border-t border-stone-100">
                      <td className="py-1 pr-3 font-mono">{row.t}</td>
                      <td className="py-1 pr-3 font-mono">{row.r}</td>
                      <td className="py-1 pr-3 font-mono">{formatBlock(row.d, model.m)}</td>
                      <td className="py-1 pr-3 font-mono">{row.rNext}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </>
        )}
      </div>

      <div className="rounded-2xl border border-stone-200 bg-white p-4">
        <div className="text-xs font-mono text-stone-500">Orbit (a/M) in base B</div>
        {model.error || model.M === 1 ? (
          <div className="mt-3 text-sm text-stone-700">No repeating orbit to display.</div>
        ) : (
          <>
            <div className="mt-2 text-sm text-stone-700">
              numerator a selects a phase (a coset of ⟨B⟩ inside (Z/MZ)× when gcd(a,M)=1)
            </div>

            <div className="mt-3 rounded-xl border border-stone-200 p-3">
              <div className="text-xs text-stone-600">first digits (1/M)</div>
              <div className="mt-1 font-mono text-stone-900 break-words">
                0.{model.full1?.digits.slice(0, 24).map((d) => formatBlock(d, model.m)).join(" ")}
                {model.L > 24 ? " …" : ""}
              </div>
              <div className="mt-3 text-xs text-stone-600">first digits (a/M)</div>
              <div className="mt-1 font-mono text-stone-900 break-words">
                0.{model.fullA?.digits.slice(0, 24).map((d) => formatBlock(d, model.m)).join(" ")}
                {model.L > 24 ? " …" : ""}
              </div>
              <div className="mt-3 text-xs text-stone-600">phase test</div>
              <div className="mt-1 text-sm text-stone-700">
                If ⟨B⟩ is the whole unit group (full reptend prime in this mode), then changing a mostly rotates the same length-L word.
              </div>
            </div>

            <div className="mt-4 overflow-auto">
              <table className="w-full text-sm">
                <thead className="text-left text-stone-600">
                  <tr>
                    <th className="py-1 pr-3 font-medium">t</th>
                    <th className="py-1 pr-3 font-medium">r_t</th>
                    <th className="py-1 pr-3 font-medium">digit d_t</th>
                    <th className="py-1 pr-3 font-medium">r_{"t+1"}</th>
                  </tr>
                </thead>
                <tbody>
                  {model.orbitA?.rows.map((row) => (
                    <tr key={row.t} className="border-t border-stone-100">
                      <td className="py-1 pr-3 font-mono">{row.t}</td>
                      <td className="py-1 pr-3 font-mono">{row.r}</td>
                      <td className="py-1 pr-3 font-mono">{formatBlock(row.d, model.m)}</td>
                      <td className="py-1 pr-3 font-mono">{row.rNext}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </>
        )}
      </div>
    </div>
  );

  return (
    <section className="mb-8 sm:mb-10">
      <div className="flex flex-col gap-5">
        {header}
        {controls}

        <div className="grid grid-cols-1 gap-4">
          {summary}
          {goodModes}
          {orbitPanels}
          {showOverlay ? skeletonOverlay : null}
        </div>

        <div className="rounded-2xl border border-stone-200 bg-white p-4">
          <div className="text-xs font-mono text-stone-500 mb-2">Pedagogical guide</div>
          <div className="text-sm text-stone-700 leading-relaxed">
            <div className="mb-2">
              <span className="font-mono">(1)</span> The invariant object is the orbit on remainders modulo <span className="font-mono">M</span>. Changing <span className="font-mono">m</span> changes the generator <span className="font-mono">B=b^m</span>.
            </div>
            <div className="mb-2">
              <span className="font-mono">(2)</span> "Good coordinates" are choices of <span className="font-mono">m</span> where <span className="font-mono">k = B mod M</span> is small. Then the universal identity <span className="font-mono">1/M = q/(B-k)</span> makes the geometric skeleton visible.
            </div>
            <div className="mb-2">
              <span className="font-mono">(3)</span> Hit Snap on <span className="font-mono">1/97</span>. You should watch the encoding suddenly become legible as powers of 3 in 2-digit blocks.
            </div>
            <div>
              <span className="font-mono">(4)</span> The spectrum is a rough "structure meter" for the coding function over the rigid rotation <span className="font-mono">t→t+1</span>.
            </div>
          </div>
        </div>

        <div className="text-xs text-stone-500 font-mono">
          Note: This demo uses trial-division factorization for φ(M). Keep M small-ish for interactive play.
        </div>
      </div>
    </section>
  );
}
