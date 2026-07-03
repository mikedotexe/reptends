import { useEffect, useEffectEvent, useMemo, useState } from 'react';

export interface BridgeBlock {
  index: number;
  raw: number;
  incoming: number;
  leftTransfer: number;
  visible: number;
  actual: number;
  remainder: number;
  nextRemainder: number;
}

export const PRIME97_BRIDGE_EXAMPLE = {
  base: 10,
  modulus: 97,
  blockWidth: 2,
  blockBase: 100,
  quotient: 1,
  remainder: 3,
  period: 48,
  blockCount: 12,
};

export function formatBlock(value: number, width: number): string {
  return value.toString().padStart(width, '0');
}

export function buildBridgeBlocks(): BridgeBlock[] {
  const blocks: BridgeBlock[] = [];
  const { blockBase, blockCount, modulus, quotient, remainder } = PRIME97_BRIDGE_EXAMPLE;

  let raw = quotient;
  let currentRemainder = 1;
  const blockDenominator = blockBase - remainder;

  for (let index = 0; index < blockCount; index++) {
    const incoming = Math.floor((quotient * remainder ** (index + 1)) / blockDenominator);
    const leftTransfer =
      index === 0
        ? 0
        : blockBase * Math.floor((quotient * remainder ** index) / blockDenominator);
    const visible = raw + incoming - leftTransfer;
    const actual = Math.floor((blockBase * currentRemainder) / modulus);
    const nextRemainder = (blockBase * currentRemainder) % modulus;

    blocks.push({
      index,
      raw,
      incoming,
      leftTransfer,
      visible,
      actual,
      remainder: currentRemainder,
      nextRemainder,
    });

    raw *= remainder;
    currentRemainder = nextRemainder;
  }

  return blocks;
}

interface BlockCellProps {
  children: string;
  index: number;
  activeIndex: number;
  tone: 'raw' | 'carry' | 'transfer' | 'visible' | 'actual';
}

const toneStyles: Record<BlockCellProps['tone'], { base: string; active: string }> = {
  raw: {
    base: 'border-stone-200 bg-white text-stone-700',
    active: 'border-amber-400 bg-amber-100 text-amber-950 shadow-sm shadow-amber-200/70',
  },
  carry: {
    base: 'border-stone-200 bg-teal-50/60 text-teal-800',
    active: 'border-teal-500 bg-teal-600 text-white shadow-sm shadow-teal-300/50',
  },
  transfer: {
    base: 'border-stone-200 bg-rose-50/70 text-rose-800',
    active: 'border-rose-500 bg-rose-600 text-white shadow-sm shadow-rose-300/50',
  },
  visible: {
    base: 'border-stone-200 bg-emerald-50/70 text-emerald-900',
    active: 'border-emerald-500 bg-emerald-600 text-white shadow-sm shadow-emerald-300/50',
  },
  actual: {
    base: 'border-stone-200 bg-indigo-50/70 text-indigo-900',
    active: 'border-indigo-500 bg-indigo-600 text-white shadow-sm shadow-indigo-300/50',
  },
};

const BlockCell = ({ children, index, activeIndex, tone }: BlockCellProps) => {
  const isActive = index === activeIndex;
  const styles = toneStyles[tone];

  return (
    <div
      className={`flex min-w-[5.5rem] flex-col rounded-xl border px-3 py-2 text-center font-mono text-sm transition-all ${
        isActive ? styles.active : styles.base
      }`}
    >
      <span className="text-[10px] uppercase tracking-[0.18em] opacity-60">j={index}</span>
      <span className="mt-1 font-semibold">{children}</span>
    </div>
  );
};

const BridgeCarryExplorer97 = () => {
  const blocks = useMemo(() => buildBridgeBlocks(), []);
  const [activeIndex, setActiveIndex] = useState(0);
  const [isPlaying, setIsPlaying] = useState(true);
  const [speedMs, setSpeedMs] = useState(950);

  const active = blocks[activeIndex] ?? blocks[0];
  const firstIncomingCarryIndex = blocks.find((block) => block.incoming > 0)?.index ?? null;
  const revealedBlocks = blocks.slice(0, activeIndex + 1);
  const digitPrefix = revealedBlocks
    .map((block) => formatBlock(block.actual, PRIME97_BRIDGE_EXAMPLE.blockWidth))
    .join('');

  const advance = useEffectEvent(() => {
    setActiveIndex((current) => {
      if (current >= blocks.length - 1) {
        setIsPlaying(false);
        return current;
      }

      return current + 1;
    });
  });

  useEffect(() => {
    if (!isPlaying) {
      return;
    }

    const timer = window.setInterval(() => {
      advance();
    }, speedMs);

    return () => window.clearInterval(timer);
  }, [advance, isPlaying, speedMs]);

  const currentEquation = `d${active.index} = ${active.raw} + ${active.incoming} - ${active.leftTransfer} = ${active.visible}`;
  const currentRemainderEquation = `${PRIME97_BRIDGE_EXAMPLE.blockBase} × ${active.remainder} = ${active.actual} × ${PRIME97_BRIDGE_EXAMPLE.modulus} + ${active.nextRemainder}`;

  return (
    <div className="rounded-[1.75rem] border border-stone-200 bg-linear-to-br from-white via-stone-50 to-emerald-50/70 p-5 shadow-sm sm:p-6">
      <div className="flex flex-col gap-5 xl:flex-row xl:items-start xl:justify-between">
        <div className="max-w-3xl">
          <div className="text-xs font-bold uppercase tracking-[0.22em] text-stone-500">
            Block Coordinate
          </div>
          <h3 className="mt-2 text-xl font-serif font-semibold tracking-tight text-stone-900 sm:text-2xl">
            1/97 as raw coefficients plus the carry layer
          </h3>
          <p className="mt-3 text-sm leading-relaxed text-stone-700 sm:text-base">
            For <code>(base, N, m, B, q, k) = (10, 97, 2, 100, 1, 3)</code>, atlas claim{' '}
            <code>series_q_weighted_identity</code> gives the raw coefficients <code>qk^j = 3^j</code>,
            and <code>carry_window_transducer</code> tells us those coefficients are not the final
            2-digit blocks until the carry layer normalizes them.
          </p>
          <p className="mt-3 text-sm leading-relaxed text-stone-700">
            The digit reptend still has length <code>96</code> in base <code>10</code>, but this
            block machine runs on <code>B = 100</code>, so the block-orbit length is
            <code> ord_97(100) = 48</code>.
          </p>
        </div>

        <div className="rounded-[1.25rem] border border-stone-200 bg-white/90 p-4 text-sm text-stone-700 shadow-sm">
          <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">Example tuple</div>
          <div className="mt-2 font-mono text-sm text-stone-900">
            base=10, N=97, m=2, B=100
          </div>
          <div className="mt-1 font-mono text-sm text-stone-900">
            q=1, k=3, L=48 blocks
          </div>
          <div className="mt-3 rounded-xl bg-stone-50 px-3 py-2 font-mono text-sm text-stone-800">
            100 = 1×97 + 3
          </div>
        </div>
      </div>

      <div className="mt-6 grid gap-6 xl:grid-cols-[1.2fr_0.8fr]">
        <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
          <div className="flex flex-wrap items-center justify-between gap-3">
            <div className="flex flex-wrap items-center gap-3">
              <div className="text-sm font-semibold uppercase tracking-[0.16em] text-stone-500">
                First 12 two-digit blocks
              </div>
              {firstIncomingCarryIndex != null ? (
                <div className="rounded-full bg-amber-100 px-3 py-1 text-xs font-bold uppercase tracking-wide text-amber-900">
                  first incoming carry at j={firstIncomingCarryIndex}
                </div>
              ) : null}
            </div>

            <div className="flex flex-wrap items-center gap-2">
              <button
                type="button"
                onClick={() => {
                  if (activeIndex >= blocks.length - 1) {
                    setActiveIndex(0);
                    setIsPlaying(true);
                    return;
                  }
                  setIsPlaying((value) => !value);
                }}
                className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
              >
                {isPlaying ? 'Pause' : activeIndex >= blocks.length - 1 ? 'Replay' : 'Play'}
              </button>
              <button
                type="button"
                onClick={() => {
                  setIsPlaying(false);
                  setActiveIndex((current) => Math.min(current + 1, blocks.length - 1));
                }}
                className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
              >
                Step
              </button>
              <button
                type="button"
                onClick={() => {
                  setIsPlaying(false);
                  setActiveIndex(0);
                }}
                className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
              >
                Reset
              </button>
              <label className="flex items-center gap-2 rounded-full border border-stone-300 px-3 py-1.5 text-sm text-stone-700">
                <span>Speed</span>
                <input
                  type="range"
                  min={350}
                  max={1400}
                  step={100}
                  value={speedMs}
                  onChange={(event) => setSpeedMs(Number(event.target.value))}
                  className="w-20 accent-stone-800"
                />
              </label>
            </div>
          </div>

          <div className="mt-4 space-y-3 overflow-x-auto pb-1">
            <div className="flex items-center gap-3">
              <div className="w-32 shrink-0 text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Raw qk^j
              </div>
              <div className="flex gap-2">
                {blocks.map((block) => (
                  <BlockCell
                    key={`raw-${block.index}`}
                    index={block.index}
                    activeIndex={activeIndex}
                    tone="raw"
                  >
                    {String(block.raw)}
                  </BlockCell>
                ))}
              </div>
            </div>

            <div className="flex items-center gap-3">
              <div className="w-32 shrink-0 text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Incoming c_j
              </div>
              <div className="flex gap-2">
                {blocks.map((block) => (
                  <BlockCell
                    key={`carry-${block.index}`}
                    index={block.index}
                    activeIndex={activeIndex}
                    tone="carry"
                  >
                    {String(block.incoming)}
                  </BlockCell>
                ))}
              </div>
            </div>

            <div className="flex items-center gap-3">
              <div className="w-32 shrink-0 text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Subtract 100c_(j-1)
              </div>
              <div className="flex gap-2">
                {blocks.map((block) => (
                  <BlockCell
                    key={`transfer-${block.index}`}
                    index={block.index}
                    activeIndex={activeIndex}
                    tone="transfer"
                  >
                    {String(block.leftTransfer)}
                  </BlockCell>
                ))}
              </div>
            </div>

            <div className="flex items-center gap-3">
              <div className="w-32 shrink-0 text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Visible d_j
              </div>
              <div className="flex gap-2">
                {blocks.map((block) => (
                  <BlockCell
                    key={`visible-${block.index}`}
                    index={block.index}
                    activeIndex={activeIndex}
                    tone="visible"
                  >
                    {formatBlock(block.visible, PRIME97_BRIDGE_EXAMPLE.blockWidth)}
                  </BlockCell>
                ))}
              </div>
            </div>

            <div className="flex items-center gap-3">
              <div className="w-32 shrink-0 text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Long division
              </div>
              <div className="flex gap-2">
                {blocks.map((block) => (
                  <BlockCell
                    key={`actual-${block.index}`}
                    index={block.index}
                    activeIndex={activeIndex}
                    tone="actual"
                  >
                    {formatBlock(block.actual, PRIME97_BRIDGE_EXAMPLE.blockWidth)}
                  </BlockCell>
                ))}
              </div>
            </div>
          </div>
        </div>

        <aside className="space-y-4">
          <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
            <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
              Current Block
            </div>
            <div className="mt-3 rounded-2xl bg-stone-50 p-4">
              <div className="text-sm font-semibold text-stone-900">j = {active.index}</div>
              <div className="mt-2 font-mono text-sm leading-relaxed text-stone-800">
                {currentEquation}
              </div>
              <div className="mt-2 font-mono text-sm leading-relaxed text-stone-800">
                {currentRemainderEquation}
              </div>
            </div>
            <div className="mt-4 rounded-2xl bg-emerald-50 px-4 py-3">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-emerald-800">
                Visible prefix
              </div>
              <div className="mt-2 font-mono text-sm text-emerald-950">
                0.{digitPrefix}
                {activeIndex < blocks.length - 1 ? '…' : ''}
              </div>
            </div>
          </div>

          <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4 text-sm leading-relaxed text-stone-700">
            <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
              Reading Guide
            </div>
            <p className="mt-3">
              For blocks <code>j = 0, 1, 2, 3</code>, the carry row is still zero, so the visible
              blocks are literally the raw coefficients <code>01, 03, 09, 27</code>.
            </p>
            <p className="mt-3">
              At <code>j = 4</code>, incoming carry begins because{' '}
              <code>3^(j+1) = 3^5 = 243 ≥ 97 = B-k</code>. That is exactly the threshold behavior
              tracked by atlas claim <code>incoming_carry_position_formula</code>.
            </p>
            <p className="mt-3">
              After that, each block is a small algebraic negotiation: raw coefficient, plus tail
              carry from the right, minus the packet sent left. The final row shows that this matches
              long division block-for-block.
            </p>
          </div>
        </aside>
      </div>
    </div>
  );
};

export default BridgeCarryExplorer97;
