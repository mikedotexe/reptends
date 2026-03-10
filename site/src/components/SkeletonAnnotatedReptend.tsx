import { useMemo } from 'react';

interface SkeletonAnnotatedReptendProps {
  /** The reptend digit string */
  reptend: string;
  /** Block width (number of digits per block) */
  m: number;
  /** Bridge residue k = B mod M */
  k: number;
  /** Quotient q from B = qM + k */
  q: number;
  /** Maximum blocks to display (default 12) */
  maxBlocks?: number;
  /** Show exponent labels beneath blocks */
  showExponents?: boolean;
}

interface BlockData {
  /** The actual block digits from the reptend */
  actual: string;
  /** The raw skeleton value: q × k^j */
  rawSkeleton: number;
  /** The raw skeleton as m-digit string */
  rawSkeletonStr: string;
  /** Whether actual matches raw skeleton (before carry) */
  matches: boolean;
  /** Block index j */
  index: number;
}

/**
 * Format a number as superscript
 */
function toSuperscript(n: number): string {
  const superscripts: Record<string, string> = {
    '0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴',
    '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹'
  };
  return n.toString().split('').map(d => superscripts[d] || d).join('');
}

/**
 * Annotated reptend display showing skeleton blocks k^j within the digit string.
 *
 * This makes the geometric series structure literal and visible:
 * - Blocks are separated with alternating colors
 * - k^j exponent labels appear beneath each block
 * - Green indicates raw skeleton matches, amber indicates carry modification
 */
const SkeletonAnnotatedReptend = ({
  reptend,
  m,
  k,
  q,
  maxBlocks = 12,
  showExponents = true,
}: SkeletonAnnotatedReptendProps) => {
  const blocks = useMemo<BlockData[]>(() => {
    const result: BlockData[] = [];
    const B = Math.pow(10, m);

    // Split reptend into m-digit blocks
    for (let j = 0; j < Math.min(maxBlocks, Math.floor(reptend.length / m)); j++) {
      const actual = reptend.slice(j * m, (j + 1) * m);
      const rawSkeleton = q * Math.pow(k, j);

      // Format raw skeleton as m-digit string (may overflow)
      const rawSkeletonStr = rawSkeleton < B
        ? rawSkeleton.toString().padStart(m, '0')
        : `[${rawSkeleton}]`;

      // Check if actual matches raw skeleton (before any carry)
      const matches = actual === rawSkeleton.toString().padStart(m, '0');

      result.push({
        actual,
        rawSkeleton,
        rawSkeletonStr,
        matches,
        index: j,
      });
    }

    return result;
  }, [reptend, m, k, q, maxBlocks]);

  // Count matches for visibility score
  const matchCount = blocks.filter(b => b.matches).length;
  const visibilityScore = blocks.length > 0 ? matchCount / blocks.length : 0;

  // Special case: k=1 means constant skeleton
  const isConstantSkeleton = k === 1;

  return (
    <div className="space-y-3">
      {/* Block row with digits */}
      <div className="overflow-x-auto">
        <div className="inline-flex items-start font-mono text-sm">
          <span className="text-stone-500 mr-1">0.</span>
          {blocks.map((block, i) => (
            <div key={i} className="flex flex-col items-center">
              {/* The actual digit block */}
              <div
                className={`px-1 py-0.5 border-r border-stone-300 last:border-r-0 ${
                  i % 2 === 0 ? 'bg-emerald-50' : 'bg-indigo-50'
                } ${
                  block.matches
                    ? 'text-emerald-700'
                    : 'text-amber-700'
                }`}
              >
                {block.actual.split('').map((d, di) => (
                  <span key={di} className={d === '0' ? 'text-stone-400' : ''}>
                    {d}
                  </span>
                ))}
              </div>

              {/* Exponent label beneath */}
              {showExponents && (
                <div className="text-[10px] text-stone-500 mt-1">
                  {isConstantSkeleton ? (
                    <span className="text-emerald-600">{q}</span>
                  ) : (
                    <span>
                      {k}{toSuperscript(block.index)}
                      {q !== 1 && <span className="text-stone-400">·{q}</span>}
                    </span>
                  )}
                </div>
              )}
            </div>
          ))}
          <span className="text-stone-400 ml-1">...</span>
        </div>
      </div>

      {/* Summary line */}
      <div className="text-xs text-stone-600 flex flex-wrap gap-3 items-center">
        <span>
          <span className="font-medium">Visibility:</span>{' '}
          <span className={visibilityScore >= 0.5 ? 'text-emerald-600' : 'text-amber-600'}>
            {matchCount}/{blocks.length} blocks match raw skeleton
          </span>
        </span>

        {isConstantSkeleton && (
          <span className="bg-emerald-100 text-emerald-700 px-2 py-0.5 rounded text-[10px] font-medium">
            k=1: constant skeleton (all blocks = {q})
          </span>
        )}

        {!isConstantSkeleton && visibilityScore < 1 && (
          <span className="text-stone-500">
            <span className="text-amber-600">amber</span> = carry modified
          </span>
        )}
      </div>

      {/* Raw skeleton comparison for k > 1 */}
      {!isConstantSkeleton && (
        <details className="text-xs">
          <summary className="text-stone-500 cursor-pointer hover:text-stone-700">
            Raw skeleton values (before carry)
          </summary>
          <div className="mt-2 font-mono text-[11px] bg-stone-100 rounded p-2 overflow-x-auto">
            <div className="flex gap-2 flex-wrap">
              {blocks.map((block, i) => (
                <span key={i} className="text-stone-600">
                  <span className="text-stone-400">{k}{toSuperscript(block.index)}·{q}=</span>
                  <span className={block.matches ? 'text-emerald-600' : 'text-amber-600'}>
                    {block.rawSkeletonStr}
                  </span>
                </span>
              ))}
            </div>
          </div>
        </details>
      )}
    </div>
  );
};

export default SkeletonAnnotatedReptend;
