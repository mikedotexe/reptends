interface OrbitClockProps {
  /** Prime modulus */
  p?: number;
  /** The orbit sequence (powers of k mod p) */
  orbit?: number[];
  /** Current animation step (0 = none visited) */
  currentStep?: number;
  /** Maximum steps in animation */
  maxSteps?: number;
}

/**
 * Visualizes the orbit of a generator k through residues mod p.
 * Shows quadratic residues highlighted, with animation of visited residues.
 */
const OrbitClock = ({
  p = 19,
  orbit = [5, 6, 11, 17, 9, 7, 16, 4, 1],
  currentStep = 0,
  maxSteps = 9,
}: OrbitClockProps) => {
  const qrSet = new Set(orbit);

  const getPosition = (residue: number, radius = 85) => {
    const angle = (residue / p) * 2 * Math.PI - Math.PI / 2;
    return {
      x: 100 + Math.cos(angle) * radius,
      y: 100 + Math.sin(angle) * radius,
    };
  };

  const visitedCount = Math.min(currentStep, maxSteps);
  const pathPoints = orbit.slice(0, visitedCount).map((r) => getPosition(r));
  const pathD =
    pathPoints.length > 0
      ? `M ${getPosition(1).x} ${getPosition(1).y} ` +
        pathPoints.map((pt) => `L ${pt.x} ${pt.y}`).join(' ')
      : '';

  return (
    <div className="flex flex-col items-center">
      <svg viewBox="0 0 200 200" className="w-40 h-40 sm:w-48 sm:h-48">
        {/* Outer circle */}
        <circle
          cx="100"
          cy="100"
          r="90"
          fill="none"
          stroke="#d6d3d1"
          strokeWidth="1"
        />

        {/* Residue dots */}
        {Array.from({ length: p - 1 }, (_, i) => i + 1).map((r) => {
          const pos = getPosition(r);
          const isQR = qrSet.has(r);
          const visitedIndex = orbit.indexOf(r);
          const isVisited = visitedIndex !== -1 && visitedIndex < visitedCount;
          const isCurrent = visitedIndex === visitedCount - 1;

          return (
            <g key={r}>
              <circle
                cx={pos.x}
                cy={pos.y}
                r={isVisited ? 6 : isQR ? 4 : 3}
                fill={
                  isCurrent
                    ? '#10b981'
                    : isVisited
                    ? '#6ee7b7'
                    : isQR
                    ? '#a8a29e'
                    : '#e7e5e4'
                }
                stroke={isQR ? '#78716c' : 'none'}
                strokeWidth="1"
                className="transition-all duration-300"
              />
              {isQR && (
                <text
                  x={pos.x}
                  y={pos.y + (pos.y > 100 ? 16 : -10)}
                  textAnchor="middle"
                  className={`text-[8px] sm:text-[9px] font-mono transition-all duration-300 ${
                    isVisited
                      ? 'fill-emerald-700 font-bold'
                      : 'fill-stone-400'
                  }`}
                >
                  {r}
                </text>
              )}
            </g>
          );
        })}

        {/* Starting point (1) */}
        <circle
          cx={getPosition(1).x}
          cy={getPosition(1).y}
          r={currentStep > 0 ? 5 : 6}
          fill={currentStep > 0 ? '#6ee7b7' : '#10b981'}
          className="transition-all duration-300"
        />
        <text
          x={getPosition(1).x}
          y={getPosition(1).y - 12}
          textAnchor="middle"
          className="text-[8px] sm:text-[9px] font-mono fill-emerald-700 font-bold"
        >
          1
        </text>

        {/* Path trace */}
        {pathD && (
          <path
            d={pathD}
            fill="none"
            stroke="#10b981"
            strokeWidth="2"
            strokeLinecap="round"
            strokeLinejoin="round"
            className="transition-all duration-500"
            style={{ opacity: 0.6 }}
          />
        )}

        {/* Current position pulse */}
        {visitedCount > 0 && pathPoints.length > 0 && (
          <circle
            cx={pathPoints[pathPoints.length - 1]?.x}
            cy={pathPoints[pathPoints.length - 1]?.y}
            r="10"
            fill="none"
            stroke="#10b981"
            strokeWidth="2"
            className="animate-pulse"
          />
        )}

        {/* Center label */}
        <text
          x="100"
          y="100"
          textAnchor="middle"
          dominantBaseline="middle"
          className="text-[10px] sm:text-xs font-mono fill-stone-400"
        >
          mod {p}
        </text>
      </svg>

      {/* Legend */}
      <div className="text-[9px] sm:text-[10px] font-mono text-stone-500 mt-2 text-center">
        <span className="inline-flex items-center gap-1 mr-3">
          <span className="w-2 h-2 rounded-full bg-stone-400 border border-stone-500"></span>{' '}
          QR
        </span>
        <span className="inline-flex items-center gap-1">
          <span className="w-2 h-2 rounded-full bg-emerald-500"></span>{' '}
          visited
        </span>
      </div>
    </div>
  );
};

export default OrbitClock;
