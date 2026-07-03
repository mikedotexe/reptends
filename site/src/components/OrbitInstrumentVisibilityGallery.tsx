import type { ReactNode } from 'react';

type DiagramKind = 'readout' | 'orbit' | 'signal' | 'window' | 'trace' | 'optics';

interface StoryPanel {
  number: string;
  title: string;
  standardLabel: string;
  body: string;
  formula: string;
  diagram: DiagramKind;
}

interface TrioCase {
  n: string;
  tuple: string;
  headline: string;
  body: string;
  events: string[];
  tone: 'emerald' | 'amber' | 'sky';
}

const traceCommand =
  'search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996';
const workbenchCommand =
  'search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20';
const baseCompareCommand =
  'search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20';
const instrumentAtlasCommand =
  'search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20';
const chartInvarianceCommand =
  'search-reptends chart-invariance --max 1200 --bases 7,10,12,30 --blocks 8 --top 20';

const storyPanels: StoryPanel[] = [
  {
    number: '01',
    title: 'Digits Are the Readout',
    standardLabel: 'finite-window trace',
    body:
      'The decimal blocks are the readout of an arithmetic process. They are faithful, but they are still an observation made in a chosen positional coordinate.',
    formula: 'observed blocks: 01 03 09 27 83',
    diagram: 'readout',
  },
  {
    number: '02',
    title: 'Source: Remainder Orbit',
    standardLabel: 'remainder orbit',
    body:
      'The source is the cyclic remainder state under the block base. Cycle index j names where we are in that orbit before the carry window observes it.',
    formula: 'r -> B*r mod M',
    diagram: 'orbit',
  },
  {
    number: '03',
    title: 'Signal: Raw Coefficient Stream',
    standardLabel: 'raw coefficient stream',
    body:
      'In a positive-q block coordinate B = qM + k, the exact coefficient stream is qk^j. Literal powers of k appear only in the special q = 1 case.',
    formula: 'coefficient_j = qk^j',
    diagram: 'signal',
  },
  {
    number: '04',
    title: 'Instrument: Finite Carry Window',
    standardLabel: 'carry-propagated block normalization',
    body:
      'Carries are the measurement apparatus of positional notation. The finite carry window folds the raw stream into admissible base-B blocks.',
    formula: 'carry_in + qk^j -> block + carry_out',
    diagram: 'window',
  },
  {
    number: '05',
    title: 'Observed Trace: Reptend Blocks',
    standardLabel: 'displayed reptend',
    body:
      'After normalization, the displayed blocks align with long division. The reptend is the observed trace, not a separate source object.',
    formula: 'raw signal + carry window = visible blocks',
    diagram: 'trace',
  },
  {
    number: '06',
    title: 'Visibility Optics',
    standardLabel: 'open research lens',
    body:
      'The bold next question is when the source orbit is readable through the finite carry window. That is a direction, with global visibility still open.',
    formula: 'source readability through a finite instrument',
    diagram: 'optics',
  },
];

const trioCases: TrioCase[] = [
  {
    n: '21',
    tuple: 'm=6, B=10^6, q=47619, k=1',
    headline: 'One-state carry collapse',
    body:
      'The canonical 21 trace keeps the carry state collapsed and the raw coefficient already visible across the window.',
    events: ['carry_free_raw throughout', 'one reachable carry state', 'factorization behaves as a direct relabeling'],
    tone: 'emerald',
  },
  {
    n: '97',
    tuple: 'm=2, B=100, q=1, k=3',
    headline: 'Delayed carry becomes visible',
    body:
      'The 97 trace separates incoming carry from local overflow, which is exactly why a block table alone feels one step too flat.',
    events: [
      'position 4: incoming_carry_before_overflow',
      'position 5: local_overflow',
      'regime: quotient_candidate_only',
    ],
    tone: 'amber',
  },
  {
    n: '996',
    tuple: 'stripped core M=249, m=3, B=1000',
    headline: 'Composite/preperiod version',
    body:
      'The 996 trace repeats the delayed carry pattern after stripping the base factor, so the same lens works beyond the prime-only story.',
    events: ['same delayed carry pattern', 'stripped periodic modulus 249', 'composite/preperiod context stays explicit'],
    tone: 'sky',
  },
];

const sourceLinks = [
  {
    label: 'Outside reader doorway',
    path: 'docs/OUTSIDE_READER_DOORWAY.md',
    href: 'https://github.com/mikedotexe/reptends/blob/main/docs/OUTSIDE_READER_DOORWAY.md',
  },
  {
    label: 'Orbit, Instrument, Visibility note',
    path: 'docs/ORBIT_INSTRUMENT_VISIBILITY.md',
    href: 'https://github.com/mikedotexe/reptends/blob/main/docs/ORBIT_INSTRUMENT_VISIBILITY.md',
  },
  {
    label: 'Carry transducer trace lens',
    path: 'docs/CARRY_TRANSDUCER.md',
    href: 'https://github.com/mikedotexe/reptends/blob/main/docs/CARRY_TRANSDUCER.md',
  },
  {
    label: 'Visibility Optics workbench guide',
    path: 'docs/VISIBILITY_OPTICS_WORKBENCH.md',
    href: 'https://github.com/mikedotexe/reptends/blob/main/docs/VISIBILITY_OPTICS_WORKBENCH.md',
  },
  {
    label: 'Instrument Atlas',
    path: 'docs/INSTRUMENT_ATLAS.md',
    href: 'https://github.com/mikedotexe/reptends/blob/main/docs/INSTRUMENT_ATLAS.md',
  },
  {
    label: 'Visibility Geometry',
    path: 'docs/VISIBILITY_GEOMETRY.md',
    href: 'https://github.com/mikedotexe/reptends/blob/main/docs/VISIBILITY_GEOMETRY.md',
  },
  {
    label: 'Chart Invariance',
    path: 'docs/CHART_INVARIANCE.md',
    href: 'https://github.com/mikedotexe/reptends/blob/main/docs/CHART_INVARIANCE.md',
  },
];

const toneStyles: Record<TrioCase['tone'], string> = {
  emerald: 'border-emerald-200 bg-emerald-50 text-emerald-950',
  amber: 'border-amber-200 bg-amber-50 text-amber-950',
  sky: 'border-sky-200 bg-sky-50 text-sky-950',
};

const DiagramShell = ({ children }: { children: ReactNode }) => (
  <div className="h-36 rounded-md border border-stone-200 bg-white p-2">
    <svg viewBox="0 0 360 140" role="img" className="h-full w-full">
      {children}
    </svg>
  </div>
);

const MiniDiagram = ({ kind }: { kind: DiagramKind }) => {
  if (kind === 'readout') {
    const blocks = ['01', '03', '09', '27', '83'];
    return (
      <DiagramShell>
        <rect x="26" y="38" width="308" height="56" rx="6" fill="#fafaf9" stroke="#d6d3d1" />
        {blocks.map((block, index) => (
          <g key={block}>
            <rect
              x={42 + index * 58}
              y="50"
              width="42"
              height="32"
              rx="4"
              fill={index === 4 ? '#ecfdf5' : '#ffffff'}
              stroke={index === 4 ? '#10b981' : '#a8a29e'}
            />
            <text x={63 + index * 58} y="71" textAnchor="middle" fontSize="14" fontFamily="monospace" fill="#1c1917">
              {block}
            </text>
          </g>
        ))}
        <text x="180" y="116" textAnchor="middle" fontSize="12" fill="#57534e">
          displayed blocks are the readout
        </text>
      </DiagramShell>
    );
  }

  if (kind === 'orbit') {
    const nodes = [
      { label: 'r0=1', x: 180, y: 28 },
      { label: 'r1=3', x: 278, y: 70 },
      { label: 'r2=9', x: 180, y: 112 },
      { label: 'r3=27', x: 82, y: 70 },
    ];
    return (
      <DiagramShell>
        <path d="M 180 34 C 244 34, 278 45, 278 70 C 278 95, 244 106, 180 106 C 116 106, 82 95, 82 70 C 82 45, 116 34, 180 34" fill="none" stroke="#0f766e" strokeWidth="3" />
        <path d="M 260 51 L 278 70 L 252 76" fill="none" stroke="#0f766e" strokeWidth="3" strokeLinecap="round" strokeLinejoin="round" />
        {nodes.map(node => (
          <g key={node.label}>
            <circle cx={node.x} cy={node.y} r="21" fill="#f0fdfa" stroke="#14b8a6" />
            <text x={node.x} y={node.y + 4} textAnchor="middle" fontSize="11" fontFamily="monospace" fill="#134e4a">
              {node.label}
            </text>
          </g>
        ))}
        <text x="180" y="134" textAnchor="middle" fontSize="12" fill="#57534e">
          cycle index j walks the source
        </text>
      </DiagramShell>
    );
  }

  if (kind === 'signal') {
    const bars = [
      { label: '1', height: 18 },
      { label: '3', height: 28 },
      { label: '9', height: 44 },
      { label: '27', height: 66 },
      { label: '81', height: 88 },
    ];
    return (
      <DiagramShell>
        <line x1="42" y1="110" x2="318" y2="110" stroke="#78716c" />
        {bars.map((bar, index) => (
          <g key={bar.label}>
            <rect
              x={64 + index * 48}
              y={110 - bar.height}
              width="30"
              height={bar.height}
              rx="4"
              fill={index < 4 ? '#fef3c7' : '#fed7aa'}
              stroke="#d97706"
            />
            <text x={79 + index * 48} y="126" textAnchor="middle" fontSize="11" fontFamily="monospace" fill="#44403c">
              {bar.label}
            </text>
          </g>
        ))}
        <text x="180" y="18" textAnchor="middle" fontSize="12" fill="#92400e">
          qk^j before carry normalization
        </text>
      </DiagramShell>
    );
  }

  if (kind === 'window') {
    return (
      <DiagramShell>
        <rect x="24" y="48" width="72" height="44" rx="6" fill="#f0f9ff" stroke="#0284c7" />
        <rect x="144" y="36" width="72" height="68" rx="6" fill="#fefce8" stroke="#ca8a04" />
        <rect x="264" y="48" width="72" height="44" rx="6" fill="#ecfdf5" stroke="#059669" />
        <path d="M 100 70 H 136" stroke="#57534e" strokeWidth="3" strokeLinecap="round" />
        <path d="M 128 62 L 138 70 L 128 78" fill="none" stroke="#57534e" strokeWidth="3" strokeLinecap="round" strokeLinejoin="round" />
        <path d="M 220 70 H 256" stroke="#57534e" strokeWidth="3" strokeLinecap="round" />
        <path d="M 248 62 L 258 70 L 248 78" fill="none" stroke="#57534e" strokeWidth="3" strokeLinecap="round" strokeLinejoin="round" />
        <text x="60" y="73" textAnchor="middle" fontSize="12" fontFamily="monospace" fill="#075985">
          carry in
        </text>
        <text x="180" y="62" textAnchor="middle" fontSize="12" fontFamily="monospace" fill="#713f12">
          raw
        </text>
        <text x="180" y="80" textAnchor="middle" fontSize="12" fontFamily="monospace" fill="#713f12">
          qk^j
        </text>
        <text x="300" y="66" textAnchor="middle" fontSize="12" fontFamily="monospace" fill="#065f46">
          block
        </text>
        <text x="300" y="82" textAnchor="middle" fontSize="12" fontFamily="monospace" fill="#065f46">
          carry out
        </text>
        <text x="180" y="128" textAnchor="middle" fontSize="12" fill="#57534e">
          the finite carry window is the instrument
        </text>
      </DiagramShell>
    );
  }

  if (kind === 'trace') {
    const rows = [
      ['raw', '1', '3', '9', '27', '81'],
      ['carry', '0', '0', '0', '0', '+2'],
      ['seen', '01', '03', '09', '27', '83'],
    ];
    return (
      <DiagramShell>
        {rows.map((row, rowIndex) => (
          <g key={row[0]}>
            <text x="40" y={35 + rowIndex * 35} textAnchor="end" fontSize="12" fill="#57534e">
              {row[0]}
            </text>
            {row.slice(1).map((value, index) => (
              <g key={`${row[0]}-${value}-${index}`}>
                <rect
                  x={58 + index * 52}
                  y={20 + rowIndex * 35}
                  width="38"
                  height="24"
                  rx="4"
                  fill={rowIndex === 2 ? '#eef2ff' : '#ffffff'}
                  stroke={rowIndex === 2 ? '#6366f1' : '#d6d3d1'}
                />
                <text x={77 + index * 52} y={36 + rowIndex * 35} textAnchor="middle" fontSize="12" fontFamily="monospace" fill="#1c1917">
                  {value}
                </text>
              </g>
            ))}
          </g>
        ))}
        <text x="180" y="132" textAnchor="middle" fontSize="12" fill="#57534e">
          aligned with long division
        </text>
      </DiagramShell>
    );
  }

  return (
    <DiagramShell>
      <path d="M 42 70 C 88 30, 136 30, 182 70 C 136 110, 88 110, 42 70 Z" fill="#f0fdfa" stroke="#0f766e" strokeWidth="3" />
      <circle cx="112" cy="70" r="20" fill="#ccfbf1" stroke="#0f766e" strokeWidth="3" />
      <rect x="210" y="42" width="108" height="56" rx="6" fill="#f8fafc" stroke="#64748b" />
      <path d="M 136 70 H 202" stroke="#57534e" strokeWidth="3" strokeLinecap="round" />
      <path d="M 194 62 L 204 70 L 194 78" fill="none" stroke="#57534e" strokeWidth="3" strokeLinecap="round" strokeLinejoin="round" />
      <text x="112" y="124" textAnchor="middle" fontSize="12" fill="#134e4a">
        source orbit
      </text>
      <text x="264" y="66" textAnchor="middle" fontSize="12" fontFamily="monospace" fill="#334155">
        readable?
      </text>
      <text x="264" y="84" textAnchor="middle" fontSize="12" fill="#334155">
        open
      </text>
    </DiagramShell>
  );
};

const OrbitInstrumentVisibilityGallery = () => {
  return (
    <section className="mb-8 sm:mb-10" aria-labelledby="orbit-instrument-visibility-title">
      <div className="mb-5 grid gap-5 lg:grid-cols-[1.15fr_0.85fr] lg:items-end">
        <div>
          <p className="text-xs font-bold uppercase text-stone-500">
            Orbit, Instrument, Visibility
          </p>
          <h2
            id="orbit-instrument-visibility-title"
            className="mt-2 text-2xl font-serif font-semibold text-stone-900 sm:text-3xl"
          >
            The entity above the digits, shown as a trace pipeline
          </h2>
          <p className="mt-4 max-w-3xl text-sm leading-relaxed text-stone-700 sm:text-base">
            The reptend is the observed trace; the remainder orbit is the source;
            the finite carry window is the instrument. This gallery is a first-draft
            visual vocabulary for that lens, with theorem status kept in the
            registry and proof-status atlas.
          </p>
        </div>

        <div className="rounded-md border border-stone-200 bg-white p-4 shadow-sm">
          <div className="text-sm font-semibold text-stone-900">Trace and workbench commands</div>
          <code className="mt-3 block overflow-x-auto rounded-sm bg-stone-900 px-3 py-2 text-xs text-stone-50">
            {traceCommand}
          </code>
          <code className="mt-2 block overflow-x-auto rounded-sm bg-stone-900 px-3 py-2 text-xs text-stone-50">
            {workbenchCommand}
          </code>
          <code className="mt-2 block overflow-x-auto rounded-sm bg-stone-900 px-3 py-2 text-xs text-stone-50">
            {baseCompareCommand}
          </code>
          <code className="mt-2 block overflow-x-auto rounded-sm bg-stone-900 px-3 py-2 text-xs text-stone-50">
            {instrumentAtlasCommand}
          </code>
          <code className="mt-2 block overflow-x-auto rounded-sm bg-stone-900 px-3 py-2 text-xs text-stone-50">
            {chartInvarianceCommand}
          </code>
          <p className="mt-3 text-sm leading-relaxed text-stone-700">
            The trace aligns remainder orbit states and carry events. The
            Visibility Optics workbench ranks finite-window evidence, and the
            base-instrument comparison asks which signals persist when the
            chosen base changes. The Instrument Atlas compares bases by what
            they reveal, absorb, distort, or obstruct. Visibility Geometry
            connects the same lens to phase space, capacity thresholds, and
            base charts. Chart Invariance compares chart pairs for invariant
            candidates and clean distortion witnesses. None of these prove
            global visibility or DFA factorization.
          </p>
        </div>
      </div>

      <div className="grid gap-4 lg:grid-cols-3">
        {storyPanels.map(panel => (
          <article key={panel.number} className="rounded-lg border border-stone-200 bg-white p-4 shadow-sm">
            <div className="flex items-center justify-between gap-3">
              <span className="rounded-sm border border-stone-200 bg-stone-50 px-2 py-1 text-xs font-semibold text-stone-600">
                {panel.number}
              </span>
              <code className="rounded-sm bg-stone-100 px-2 py-1 text-[11px] text-stone-600">
                {panel.standardLabel}
              </code>
            </div>
            <h3 className="mt-3 text-base font-serif font-semibold text-stone-900">
              {panel.title}
            </h3>
            <p className="mt-2 min-h-24 text-sm leading-relaxed text-stone-700">
              {panel.body}
            </p>
            <MiniDiagram kind={panel.diagram} />
            <code className="mt-3 block rounded-sm bg-stone-50 px-3 py-2 text-xs text-stone-700">
              {panel.formula}
            </code>
          </article>
        ))}
      </div>

      <div className="mt-5 grid gap-4 lg:grid-cols-3">
        {trioCases.map(caseStudy => (
          <article key={caseStudy.n} className={`rounded-lg border p-4 shadow-sm ${toneStyles[caseStudy.tone]}`}>
            <div className="flex flex-wrap items-center gap-2">
              <div className="text-lg font-serif font-semibold">1/{caseStudy.n}</div>
              <code className="rounded-sm bg-white/75 px-2 py-1 text-[11px] text-stone-700">
                {caseStudy.tuple}
              </code>
            </div>
            <h3 className="mt-3 text-sm font-semibold">{caseStudy.headline}</h3>
            <p className="mt-2 text-sm leading-relaxed">{caseStudy.body}</p>
            <ul className="mt-3 space-y-2 text-sm">
              {caseStudy.events.map(event => (
                <li key={event} className="flex gap-2">
                  <span aria-hidden="true">-</span>
                  <span>{event}</span>
                </li>
              ))}
            </ul>
          </article>
        ))}
      </div>

      <div className="mt-5 grid gap-4 lg:grid-cols-[0.9fr_1.1fr]">
        <div className="rounded-md border border-stone-200 bg-white p-4 shadow-sm">
          <h3 className="text-sm font-semibold text-stone-900">Status boundary</h3>
          <p className="mt-2 text-sm leading-relaxed text-stone-700">
            This is reader-facing language, not a new theorem claim. The exact
            supports remain <code>series_q_weighted_identity</code>,
            <code> positive_q_good_modes</code>, and the implemented carry
            transducer surfaces. The claims <code>carry_dfa_factorization</code>
            and <code> small_k_visibility_threshold</code> remain open.
          </p>
        </div>

        <div className="rounded-md border border-stone-200 bg-white p-4 shadow-sm">
          <h3 className="text-sm font-semibold text-stone-900">Follow the trail</h3>
          <div className="mt-3 grid gap-3 sm:grid-cols-2">
            {sourceLinks.map(link => (
              <a
                key={link.path}
                href={link.href}
                target="_blank"
                rel="noreferrer"
                className="rounded-md border border-stone-200 bg-stone-50 p-3 text-sm transition-colors hover:border-stone-300 hover:bg-white"
              >
                <span className="font-semibold text-stone-900">{link.label}</span>
                <code className="mt-2 block text-xs text-stone-600">{link.path}</code>
              </a>
            ))}
          </div>
        </div>
      </div>
    </section>
  );
};

export default OrbitInstrumentVisibilityGallery;
