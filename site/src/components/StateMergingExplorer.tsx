import { useState } from 'react';
import {
  stateMergingCaseStudies,
  stateMergingFamilyStudies,
  stateMergingResearchLayer,
  stateMergingSameCoreResearchLayer,
  type StateAlignmentRow,
  type StateMergingCaseStudyRecord,
} from '../lib/atlas';

type Direction = 'forward' | 'reverse';
type Selection =
  | { kind: 'source'; source: number }
  | { kind: 'target'; target: number }
  | { kind: 'edge'; source: number; target: number }
  | null;

interface GraphEdge {
  source: number;
  target: number;
  count: number;
  positions: number[];
}

const visibleCompressionFamily = stateMergingFamilyStudies.find(
  family => family.members.join(',') === '249,498,996'
);

const mixedObstructionFamily = stateMergingFamilyStudies.find(
  family => family.members.join(',') === '17,34,68,85'
);

const familyResearchByCore = new Map(
  stateMergingSameCoreResearchLayer.rows.map(row => [row.core_n, row])
);

const familyModes = [
  {
    key: 'family-249',
    label: '249 / 498 / 996',
    record: visibleCompressionFamily,
    researchRow: familyResearchByCore.get(249) ?? visibleCompressionFamily?.family_row ?? null,
  },
  {
    key: 'family-17',
    label: '17 / 34 / 68 / 85',
    record: mixedObstructionFamily,
    researchRow: familyResearchByCore.get(17) ?? mixedObstructionFamily?.family_row ?? null,
  },
].filter(
  (
    mode
  ): mode is {
    key: string;
    label: string;
    record: NonNullable<typeof visibleCompressionFamily>;
    researchRow: NonNullable<(typeof stateMergingSameCoreResearchLayer.rows)[number]>;
  } => Boolean(mode.record)
);

const caseOrder = [21, 97, 89, 996];

function selectedProfile(caseRecord: StateMergingCaseStudyRecord, direction: Direction) {
  return direction === 'forward'
    ? caseRecord.forward_profile
    : caseRecord.reverse_profile;
}

function edgeRows(caseRecord: StateMergingCaseStudyRecord, direction: Direction): GraphEdge[] {
  const counts = new Map<string, GraphEdge>();
  for (const row of caseRecord.alignment_rows) {
    const source = direction === 'forward' ? row.remainder_state : row.carry_state;
    const target = direction === 'forward' ? row.carry_state : row.remainder_state;
    const key = `${source}:${target}`;
    const existing = counts.get(key);
    if (existing) {
      existing.count += 1;
      existing.positions.push(row.position);
      continue;
    }
    counts.set(key, {
      source,
      target,
      count: 1,
      positions: [row.position],
    });
  }
  return Array.from(counts.values()).sort(
    (left, right) =>
      left.source - right.source || left.target - right.target
  );
}

function filteredRows(
  rows: StateAlignmentRow[],
  direction: Direction,
  selection: Selection
) {
  if (!selection) {
    return rows;
  }
  return rows.filter(row => {
    const source = direction === 'forward' ? row.remainder_state : row.carry_state;
    const target = direction === 'forward' ? row.carry_state : row.remainder_state;
    if (selection.kind === 'source') {
      return source === selection.source;
    }
    if (selection.kind === 'target') {
      return target === selection.target;
    }
    return source === selection.source && target === selection.target;
  });
}

const regimeTone: Record<string, string> = {
  state_relabeling: 'border-emerald-200 bg-emerald-50 text-emerald-950',
  quotient_candidate_only: 'border-amber-200 bg-amber-50 text-amber-950',
  finite_word_only: 'border-rose-200 bg-rose-50 text-rose-950',
};

const obstructionTone: Record<string, string> = {
  state_relabeling: 'border-emerald-200 bg-emerald-50 text-emerald-950',
  visible_preimage_compression: 'border-amber-200 bg-amber-50 text-amber-950',
  hidden_graph_obstruction: 'border-sky-200 bg-sky-50 text-sky-950',
  finite_word_only: 'border-rose-200 bg-rose-50 text-rose-950',
};

const StateMergingExplorer = () => {
  const canonicalCases = caseOrder
    .map(n => stateMergingCaseStudies.find(caseStudy => caseStudy.n === n))
    .filter((caseStudy): caseStudy is StateMergingCaseStudyRecord => Boolean(caseStudy));
  const [selectedCase, setSelectedCase] = useState<string>('97');
  const [familyMember, setFamilyMember] = useState<number>(
    visibleCompressionFamily?.member_cases[0]?.n ?? mixedObstructionFamily?.member_cases[0]?.n ?? 249
  );
  const [direction, setDirection] = useState<Direction>('forward');
  const [selection, setSelection] = useState<Selection>(null);

  if (!canonicalCases.length) {
    return null;
  }

  const activeFamilyMode = familyModes.find(mode => mode.key === selectedCase) ?? null;
  const activeFamilyRecord = activeFamilyMode?.record ?? null;
  const activeFamilyResearch = activeFamilyMode?.researchRow ?? activeFamilyRecord?.family_row ?? null;
  const caseRecord: StateMergingCaseStudyRecord =
    activeFamilyRecord
      ? activeFamilyRecord.member_cases.find(member => member.n === familyMember) ?? activeFamilyRecord.member_cases[0]
      : canonicalCases.find(entry => String(entry.n) === selectedCase) ?? canonicalCases[0];
  const profile = selectedProfile(caseRecord, direction);
  const edges = edgeRows(caseRecord, direction);
  const rows = filteredRows(caseRecord.alignment_rows, direction, selection);
  const sourceStates = profile.fibers.map(entry => entry.source_state);
  const targetStates = profile.preimage_fibers.map(entry => entry.target_state);
  const sourceFiberSize = new Map(
    profile.fibers.map(entry => [entry.source_state, entry.target_states.length])
  );
  const targetPreimageSize = new Map(
    profile.preimage_fibers.map(entry => [entry.target_state, entry.source_states.length])
  );
  const sourceYs = new Map(
    sourceStates.map((state, index) => [
      state,
      56 + (index * 320) / Math.max(sourceStates.length - 1, 1),
    ])
  );
  const targetYs = new Map(
    targetStates.map((state, index) => [
      state,
      56 + (index * 320) / Math.max(targetStates.length - 1, 1),
    ])
  );

  return (
    <section className="mb-8 sm:mb-10">
      <div className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm sm:p-6">
        <div className="mb-5 flex flex-col gap-3 lg:flex-row lg:items-end lg:justify-between">
          <div>
            <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
              Preimage-Fiber Profile
            </div>
            <h2 className="mt-2 text-xl font-serif font-semibold text-stone-900 sm:text-2xl">
              State-Merging Atlas
            </h2>
            <p className="mt-3 max-w-3xl text-sm leading-relaxed text-stone-700 sm:text-base">
              This explorer stays on the selected Track 17 coordinate and asks a
              sharper question than “does a factorization exist?”: how many
              remainder states collapse onto each carry state on the visible
              window, and where does the reverse direction fail?
            </p>
          </div>
          <div className="rounded-lg border border-sky-100 bg-sky-50 p-4 text-sm leading-relaxed text-sky-950">
            The public object here is the finite-window preimage-fiber profile,
            not a promoted theorem. The global claim
            <code className="mx-1 rounded bg-white/80 px-1.5 py-0.5 text-[11px]">
              carry_dfa_factorization
            </code>
            remains open.
          </div>
        </div>

        <div className="mb-5 rounded-lg border border-stone-200 bg-stone-50 p-4">
          <div className="flex flex-col gap-3 lg:flex-row lg:items-start lg:justify-between">
            <div>
              <div className="text-sm font-semibold text-stone-900">
                Base-10 Selected-Coordinate Census
              </div>
              <p className="mt-2 max-w-3xl text-sm leading-relaxed text-stone-700">
                The base-10 Track 17 sweep now splits quotient-only cases into visible preimage
                compression and hidden graph obstruction. The counts below come from the published
                bounded atlas layer, while the buttons jump straight to representative canonical
                cases in this explorer.
              </p>
            </div>
            <div className="rounded-lg border border-white bg-white p-3 text-xs text-stone-600">
              {stateMergingResearchLayer.summary_lines.map(line => (
                <div key={line}>{line}</div>
              ))}
            </div>
          </div>
          <div className="mt-4 grid gap-3 md:grid-cols-3">
            <div className="rounded-lg border border-amber-200 bg-white p-3">
              <div className="text-xs font-semibold uppercase tracking-wide text-amber-700">
                Visible Compression
              </div>
              <div className="mt-2 text-2xl font-semibold text-stone-900">
                {stateMergingResearchLayer.visible_preimage_compression_count}
              </div>
              <div className="mt-3 flex flex-wrap gap-2">
                {[97, 996].map(n => (
                  <button
                    key={`visible-${n}`}
                    className="rounded-full bg-amber-50 px-3 py-1 text-xs text-amber-950 transition hover:bg-amber-100"
                    onClick={() => {
                      setSelectedCase(String(n));
                      setSelection(null);
                    }}
                    type="button"
                  >
                    1/{n}
                  </button>
                ))}
              </div>
            </div>
            <div className="rounded-lg border border-sky-200 bg-white p-3">
              <div className="text-xs font-semibold uppercase tracking-wide text-sky-700">
                Hidden Obstruction
              </div>
              <div className="mt-2 text-2xl font-semibold text-stone-900">
                {stateMergingResearchLayer.hidden_graph_obstruction_count}
              </div>
              <div className="mt-3 flex flex-wrap gap-2">
                <button
                  className="rounded-full bg-sky-50 px-3 py-1 text-xs text-sky-950 transition hover:bg-sky-100"
                  onClick={() => {
                    setSelectedCase('89');
                    setSelection(null);
                  }}
                  type="button"
                >
                  1/89
                </button>
              </div>
            </div>
            <div className="rounded-lg border border-stone-200 bg-white p-3">
              <div className="text-xs font-semibold uppercase tracking-wide text-stone-500">
                Quotient-Only Total
              </div>
              <div className="mt-2 text-2xl font-semibold text-stone-900">
                {stateMergingResearchLayer.quotient_candidate_only_count}
              </div>
              <p className="mt-3 text-sm leading-relaxed text-stone-700">
                Hidden cases keep the aligned window bijective. Visible cases already show the
                collapse in their target preimages.
              </p>
            </div>
          </div>
        </div>

        <div className="grid gap-3 lg:grid-cols-[1.25fr_0.9fr]">
          <div className="rounded-lg border border-stone-200 bg-stone-50 p-4">
            <div className="text-xs font-semibold uppercase tracking-wide text-stone-500">
              Canonical Cases
            </div>
            <div className="mt-2 flex flex-wrap gap-2">
              {canonicalCases.map(caseStudy => {
                const key = String(caseStudy.n);
                const active = selectedCase === key;
                return (
                  <button
                    key={key}
                    className={`rounded-full px-3 py-1.5 text-sm transition ${
                      active
                        ? 'bg-stone-900 text-white'
                        : 'bg-white text-stone-700 hover:bg-stone-200'
                    }`}
                    onClick={() => {
                      setSelectedCase(key);
                      setSelection(null);
                    }}
                    type="button"
                  >
                    1/{key}
                  </button>
                );
              })}
            </div>

            <div className="mt-4 text-xs font-semibold uppercase tracking-wide text-stone-500">
              Family Modes
            </div>
            <div className="mt-2 flex flex-wrap gap-2">
              {familyModes.map(mode => {
                const active = selectedCase === mode.key;
                return (
                  <button
                    key={mode.key}
                    className={`rounded-full px-3 py-1.5 text-sm transition ${
                      active
                        ? 'bg-stone-900 text-white'
                        : 'bg-white text-stone-700 hover:bg-stone-200'
                    }`}
                    onClick={() => {
                      setSelectedCase(mode.key);
                      setFamilyMember(mode.record.member_cases[0]?.n ?? familyMember);
                      setSelection(null);
                    }}
                    type="button"
                  >
                    {mode.label}
                  </button>
                );
              })}
            </div>

            {activeFamilyRecord ? (
              <div className="mt-3 rounded-lg border border-stone-200 bg-white p-3">
                <div className="text-sm font-semibold text-stone-900">
                  {activeFamilyRecord.label}
                </div>
                <p className="mt-2 text-sm leading-relaxed text-stone-700">
                  {activeFamilyRecord.explanation}
                </p>
                <div className="mt-3 flex flex-wrap gap-2">
                  {activeFamilyRecord.member_cases.map(member => (
                    <button
                      key={member.n}
                      className={`rounded-full px-3 py-1.5 text-xs transition ${
                        familyMember === member.n
                          ? 'bg-amber-600 text-white'
                          : 'bg-stone-100 text-stone-700 hover:bg-stone-200'
                      }`}
                      onClick={() => {
                        setFamilyMember(member.n);
                        setSelection(null);
                      }}
                      type="button"
                    >
                      1/{member.n}
                    </button>
                  ))}
                </div>
                <div className="mt-3 grid gap-2 md:grid-cols-3">
                  <div className="rounded-lg border border-stone-200 bg-stone-50 p-3 text-xs text-stone-600">
                    <div className="font-semibold text-stone-900">Selected Regimes</div>
                    <div className="mt-2">
                      {(activeFamilyResearch ?? activeFamilyRecord.family_row).selected_regimes.join(' | ')}
                    </div>
                  </div>
                  <div className="rounded-lg border border-stone-200 bg-stone-50 p-3 text-xs text-stone-600">
                    <div className="font-semibold text-stone-900">Obstruction Classes</div>
                    <div className="mt-2">
                      {(activeFamilyResearch ?? activeFamilyRecord.family_row).selected_obstruction_classes.join(' | ')}
                    </div>
                  </div>
                  <div className="rounded-lg border border-stone-200 bg-stone-50 p-3 text-xs text-stone-600">
                    <div className="font-semibold text-stone-900">Family Signal</div>
                    <div className="mt-2">
                      {(activeFamilyResearch ?? activeFamilyRecord.family_row)
                        .has_nonmonotone_hidden_visible_switching
                        ? 'switches between hidden and visible phases'
                        : (activeFamilyResearch ?? activeFamilyRecord.family_row)
                            .crosses_relabeling_hidden_visible_classes
                          ? 'spans relabeling, hidden, and visible'
                          : 'tracks same-core visible disagreement'}
                    </div>
                  </div>
                </div>
                <div className="mt-3 grid gap-2 md:grid-cols-2">
                  <div className="rounded-lg border border-stone-200 bg-stone-50 p-3 text-xs text-stone-600">
                    <div className="font-semibold text-stone-900">Full Family Phase Path</div>
                    <div className="mt-2">
                      {(activeFamilyResearch ?? activeFamilyRecord.family_row).compressed_class_path.join(' → ')}
                    </div>
                    <div className="mt-2 text-stone-500">
                      {(activeFamilyResearch ?? activeFamilyRecord.family_row).phase_summary}
                    </div>
                  </div>
                  <div className="rounded-lg border border-stone-200 bg-stone-50 p-3 text-xs text-stone-600">
                    <div className="font-semibold text-stone-900">Transition Landmarks</div>
                    <div className="mt-2">
                      first hidden = {(activeFamilyResearch ?? activeFamilyRecord.family_row).first_hidden_member ?? '—'}
                    </div>
                    <div className="mt-1">
                      first visible = {(activeFamilyResearch ?? activeFamilyRecord.family_row).first_visible_member ?? '—'}
                    </div>
                    <div className="mt-1">
                      onset = {(activeFamilyResearch ?? activeFamilyRecord.family_row).onset_kind.replace(/_/g, ' ')}
                    </div>
                    <div className="mt-1">
                      behavior = {(activeFamilyResearch ?? activeFamilyRecord.family_row).visibility_behavior.replace(/_/g, ' ')}
                    </div>
                    <div className="mt-1">
                      hidden/visible switches = {(activeFamilyResearch ?? activeFamilyRecord.family_row).hidden_visible_switch_count}
                    </div>
                  </div>
                </div>
              </div>
            ) : null}

            <div className="mt-4 flex flex-wrap gap-2">
              {([
                ['forward', 'Remainder → Carry'],
                ['reverse', 'Carry → Remainder'],
              ] as const).map(([value, label]) => {
                const active = direction === value;
                return (
                  <button
                    key={value}
                    className={`rounded-full px-3 py-1.5 text-sm transition ${
                      active
                        ? 'bg-amber-600 text-white'
                        : 'bg-white text-stone-700 hover:bg-stone-200'
                    }`}
                    onClick={() => {
                      setDirection(value);
                      setSelection(null);
                    }}
                    type="button"
                  >
                    {label}
                  </button>
                );
              })}
            </div>
          </div>

          <aside className="rounded-lg border border-stone-200 bg-stone-50 p-4">
            <div className="text-sm font-semibold text-stone-900">{caseRecord.label}</div>
            <p className="mt-2 text-sm leading-relaxed text-stone-700">
              {caseRecord.explanation}
            </p>
            <div
              className={`mt-4 rounded-lg border px-3 py-2 text-xs font-semibold uppercase tracking-wide ${
                regimeTone[caseRecord.factorization_regime] ?? 'border-stone-200 bg-stone-100 text-stone-700'
              }`}
            >
              {caseRecord.factorization_regime.replace(/_/g, ' ')}
            </div>
            <div
              className={`mt-2 rounded-lg border px-3 py-2 text-xs font-semibold uppercase tracking-wide ${
                obstructionTone[caseRecord.obstruction_class] ?? 'border-stone-200 bg-stone-100 text-stone-700'
              }`}
            >
              {caseRecord.obstruction_class.replace(/_/g, ' ')}
            </div>
            <div className="mt-4 grid gap-2 text-sm text-stone-700 sm:grid-cols-2">
              <div className="rounded-lg border border-stone-200 bg-white p-3">
                <div className="font-semibold text-stone-900">Coordinate</div>
                <div className="mt-2">
                  m = {caseRecord.selected_coordinate.m}, B = {caseRecord.selected_coordinate.B}
                </div>
                <div className="mt-1">
                  q = {caseRecord.selected_coordinate.q}, k = {caseRecord.selected_coordinate.k}
                </div>
              </div>
              <div className="rounded-lg border border-stone-200 bg-white p-3">
                <div className="font-semibold text-stone-900">Profile</div>
                <div className="mt-2">source states = {profile.source_state_count}</div>
                <div className="mt-1">image states = {profile.image_state_count}</div>
                <div className="mt-1">max fiber size = {profile.max_fiber_size}</div>
                <div className="mt-1">max preimage size = {profile.max_preimage_size}</div>
                <div className="mt-1">
                  alignment bijection = {caseRecord.observed_alignment_bijection ? 'yes' : 'no'}
                </div>
              </div>
            </div>
            <div className="mt-4 grid gap-2 text-sm text-stone-700 sm:grid-cols-2">
              <div className="rounded-lg border border-stone-200 bg-white p-3">
                <div className="font-semibold text-stone-900">Observed Graph Gap</div>
                <div className="mt-2">
                  states = {caseRecord.graph_state_gap > 0 ? '+' : ''}
                  {caseRecord.graph_state_gap}
                </div>
                <div className="mt-1">
                  carry {caseRecord.carry_state_count} vs remainder {caseRecord.remainder_state_count}
                </div>
              </div>
              <div className="rounded-lg border border-stone-200 bg-white p-3">
                <div className="font-semibold text-stone-900">Minimized Class Gap</div>
                <div className="mt-2">
                  classes = {caseRecord.minimized_class_gap > 0 ? '+' : ''}
                  {caseRecord.minimized_class_gap}
                </div>
                <div className="mt-1">
                  carry {caseRecord.carry_class_count} vs remainder {caseRecord.remainder_class_count}
                </div>
              </div>
            </div>
            <div className="mt-4 rounded-lg border border-stone-200 bg-white p-3 text-sm text-stone-700">
              <div className="font-semibold text-stone-900">Selected Obstruction</div>
              <p className="mt-2 leading-relaxed">{caseRecord.obstruction_summary}</p>
            </div>
            <div className="mt-4 rounded-lg border border-stone-200 bg-white p-3 text-sm text-stone-700">
              <div className="font-semibold text-stone-900">Signatures</div>
              <div className="mt-2">
                <span className="font-medium">Preimages:</span> {profile.preimage_signature}
              </div>
              <div className="mt-1">
                <span className="font-medium">Ambiguity:</span> {profile.ambiguity_signature}
              </div>
            </div>
          </aside>
        </div>

        <div className="mt-6 grid gap-6 xl:grid-cols-[1.2fr_0.85fr]">
          <div className="rounded-lg border border-stone-200 bg-stone-50 p-4">
            <div className="mb-3 flex items-center justify-between gap-3">
              <div className="text-sm font-semibold text-stone-900">
                Bipartite Compression View
              </div>
              <div className="text-xs text-stone-500">
                Click a node or edge to filter the aligned trace.
              </div>
            </div>

            <svg
              viewBox="0 0 620 380"
              className="w-full overflow-visible rounded-lg border border-stone-200 bg-white"
            >
              {edges.map(edge => {
                const y1 = sourceYs.get(edge.source) ?? 0;
                const y2 = targetYs.get(edge.target) ?? 0;
                const active =
                  !selection ||
                  (selection.kind === 'source' && selection.source === edge.source) ||
                  (selection.kind === 'target' && selection.target === edge.target) ||
                  (selection.kind === 'edge' &&
                    selection.source === edge.source &&
                    selection.target === edge.target);
                return (
                  <g key={`${edge.source}-${edge.target}`}>
                    <line
                      x1={160}
                      y1={y1}
                      x2={460}
                      y2={y2}
                      stroke={active ? '#b45309' : '#cbd5e1'}
                      strokeOpacity={active ? 0.95 : 0.55}
                      strokeWidth={1.5 + edge.count * 1.35}
                      onClick={() =>
                        setSelection({
                          kind: 'edge',
                          source: edge.source,
                          target: edge.target,
                        })
                      }
                    />
                    <text
                      x={(160 + 460) / 2}
                      y={(y1 + y2) / 2 - 6}
                      textAnchor="middle"
                      className="fill-stone-500 text-[11px]"
                    >
                      ×{edge.count}
                    </text>
                  </g>
                );
              })}

              {sourceStates.map(state => {
                const y = sourceYs.get(state) ?? 0;
                const active =
                  !selection ||
                  (selection.kind === 'source' && selection.source === state) ||
                  (selection.kind === 'edge' && selection.source === state);
                const radius = 12 + 3 * ((sourceFiberSize.get(state) ?? 1) - 1);
                return (
                  <g key={`source-${state}`}>
                    <circle
                      cx={160}
                      cy={y}
                      r={radius}
                      fill={active ? '#1f2937' : '#475569'}
                      onClick={() => setSelection({ kind: 'source', source: state })}
                    />
                    <text
                      x={128}
                      y={y + 4}
                      textAnchor="end"
                      className="fill-stone-700 text-[12px]"
                    >
                      {state}
                    </text>
                  </g>
                );
              })}

              {targetStates.map(state => {
                const y = targetYs.get(state) ?? 0;
                const active =
                  !selection ||
                  (selection.kind === 'target' && selection.target === state) ||
                  (selection.kind === 'edge' && selection.target === state);
                const radius = 12 + 4 * ((targetPreimageSize.get(state) ?? 1) - 1);
                return (
                  <g key={`target-${state}`}>
                    <circle
                      cx={460}
                      cy={y}
                      r={radius}
                      fill={active ? '#92400e' : '#d97706'}
                      onClick={() => setSelection({ kind: 'target', target: state })}
                    />
                    <text
                      x={492}
                      y={y + 4}
                      textAnchor="start"
                      className="fill-stone-700 text-[12px]"
                    >
                      {state}
                    </text>
                    <text
                      x={460}
                      y={y + 4}
                      textAnchor="middle"
                      className="fill-white text-[11px] font-semibold"
                    >
                      {targetPreimageSize.get(state)}
                    </text>
                  </g>
                );
              })}

              <text
                x={160}
                y={26}
                textAnchor="middle"
                className="fill-stone-500 text-[12px] font-semibold uppercase tracking-wide"
              >
                Source States
              </text>
              <text
                x={460}
                y={26}
                textAnchor="middle"
                className="fill-stone-500 text-[12px] font-semibold uppercase tracking-wide"
              >
                Target States
              </text>
            </svg>
          </div>

          <div className="space-y-4">
            <div className="rounded-lg border border-stone-200 bg-stone-50 p-4">
              <div className="text-sm font-semibold text-stone-900">
                {caseRecord.obstruction_class === 'visible_preimage_compression'
                  ? 'Compression Targets'
                  : 'Explicit Preimages'}
              </div>
              <div className="mt-3 space-y-2 text-sm text-stone-700">
                {profile.preimage_fibers.map(entry => (
                  <div
                    key={`preimage-${entry.target_state}`}
                    className="rounded-lg border border-stone-200 bg-white p-3"
                  >
                    <div className="font-medium text-stone-900">
                      target {entry.target_state}
                    </div>
                    <div className="mt-1">
                      sources: {entry.source_states.join(', ')}
                    </div>
                  </div>
                ))}
              </div>
            </div>

            <div className="rounded-lg border border-stone-200 bg-stone-50 p-4">
              <div className="text-sm font-semibold text-stone-900">Why It Fails</div>
              {caseRecord.obstruction_class === 'visible_preimage_compression' ? (
                <div className="mt-3 space-y-2 text-sm text-stone-700">
                  {caseRecord.compression_targets.map(entry => (
                    <div
                      key={`compression-${entry.target_state}`}
                      className="rounded-lg border border-amber-200 bg-white p-3"
                    >
                      <div className="font-medium text-stone-900">
                        carry state {entry.target_state}
                      </div>
                      <div className="mt-1">
                        merged remainders: {entry.source_states.join(', ')}
                      </div>
                    </div>
                  ))}
                </div>
              ) : profile.ambiguous_sources.length ? (
                <div className="mt-3 space-y-2 text-sm text-stone-700">
                  {profile.ambiguous_sources.map(entry => (
                    <div
                      key={`ambiguous-${entry.source_state}`}
                      className="rounded-lg border border-rose-200 bg-white p-3"
                    >
                      <div className="font-medium text-stone-900">
                        source {entry.source_state}
                      </div>
                      <div className="mt-1">
                        targets: {entry.target_states.join(', ')}
                      </div>
                    </div>
                  ))}
                </div>
              ) : (
                <div
                  className={`mt-3 rounded-lg border bg-white p-3 text-sm text-stone-700 ${
                    caseRecord.obstruction_class === 'hidden_graph_obstruction'
                      ? 'border-sky-200'
                      : 'border-emerald-200'
                  }`}
                >
                  {caseRecord.obstruction_class === 'hidden_graph_obstruction'
                    ? 'The aligned window is bijective; the obstruction lives in the graph and minimization gaps rather than visible collisions.'
                    : 'The selected direction stays functional on this window.'}
                </div>
              )}
            </div>
          </div>
        </div>

        <div className="mt-6 rounded-lg border border-stone-200 bg-stone-50 p-4">
          <div className="mb-3 flex items-center justify-between gap-3">
            <div className="text-sm font-semibold text-stone-900">Linked Trace Table</div>
            <div className="text-xs text-stone-500">
              Showing {rows.length} / {caseRecord.alignment_rows.length} aligned rows
            </div>
          </div>
          <div className="mb-3 rounded-lg border border-stone-200 bg-white p-3 text-sm text-stone-700">
            {caseRecord.obstruction_class === 'hidden_graph_obstruction'
              ? 'This filtered trace stays one-to-one at every aligned position. The missing relabeling only appears once the observed graph sizes and minimized class counts are compared.'
              : 'Click merged target nodes or thick edges to isolate the exact aligned positions where visible compression occurs.'}
          </div>
          <div className="overflow-x-auto rounded-lg border border-stone-200 bg-white">
            <table className="min-w-full text-left text-sm text-stone-700">
              <thead className="bg-stone-100 text-xs uppercase tracking-wide text-stone-500">
                <tr>
                  <th className="px-3 py-2">j</th>
                  <th className="px-3 py-2">Coefficient</th>
                  <th className="px-3 py-2">Remainder</th>
                  <th className="px-3 py-2">Carry</th>
                  <th className="px-3 py-2">Block</th>
                </tr>
              </thead>
              <tbody>
                {rows.map(row => (
                  <tr key={`${row.position}-${row.remainder_state}-${row.carry_state}`} className="border-t border-stone-200">
                    <td className="px-3 py-2 font-medium text-stone-900">{row.position}</td>
                    <td className="px-3 py-2">{row.coefficient}</td>
                    <td className="px-3 py-2">{row.remainder_state}</td>
                    <td className="px-3 py-2">{row.carry_state}</td>
                    <td className="px-3 py-2">{row.block_value}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </div>
      </div>
    </section>
  );
};

export default StateMergingExplorer;
