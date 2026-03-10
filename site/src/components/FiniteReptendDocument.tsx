import { type ReactNode, useState } from 'react';
import { Block, M } from './shared';
import CircleWalkPlayground from './CircleWalkPlayground';
import CounterexampleRegistryPanel from './CounterexampleRegistryPanel';
import CuratedExamplesPanel from './CuratedExamplesPanel';
import GoodCoordinatesExplorer from './GoodCoordinatesExplorer';
import OrbitCoreExplorer from './OrbitCoreExplorer';
import ProofAtlasPanel from './ProofAtlasPanel';
import StandardTerminologyPanel from './StandardTerminologyPanel';
import {
  canonicalExamples,
  claimById,
  displayTerm,
} from '../lib/atlas';

const statusStyles: Record<string, string> = {
  classical: 'bg-stone-200 text-stone-700',
  'reproved-here': 'bg-emerald-100 text-emerald-800',
  'implemented-here': 'bg-amber-100 text-amber-900',
  empirical: 'bg-rose-100 text-rose-800',
  open: 'bg-sky-100 text-sky-800',
};

const statusLabel: Record<string, string> = {
  classical: 'Classical',
  'reproved-here': 'Reproved Here',
  'implemented-here': 'Implemented Here',
  empirical: 'Empirical',
  open: 'Open',
};

interface ClaimCardProps {
  claimId: string;
  children?: ReactNode;
}

const ClaimCard = ({ claimId, children }: ClaimCardProps) => {
  const claim = claimById.get(claimId);
  if (!claim) {
    return null;
  }

  return (
    <article className="rounded-sm border border-stone-200 bg-white p-4 sm:p-5 shadow-sm">
      <div className="flex flex-wrap items-center gap-3 mb-3">
        <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-900">
          {claim.title}
        </h3>
        <span
          className={`rounded-full px-2.5 py-1 text-[10px] font-bold uppercase tracking-wide ${statusStyles[claim.status]}`}
        >
          {statusLabel[claim.status]}
        </span>
        <code className="rounded bg-stone-100 px-2 py-1 text-xs text-stone-700">
          {claim.id}
        </code>
      </div>
      <p className="text-sm sm:text-base leading-relaxed text-stone-700">
        {claim.statement}
      </p>
      {children}
      <div className="mt-4 text-xs text-stone-500">
        Repo status: {claim.repo_status}
      </div>
      <div className="mt-1 text-xs text-stone-500">
        Proof status: {claim.proof_status}
      </div>
    </article>
  );
};

interface VocabularyCalloutProps {
  vocabularyId: string;
  standardMode: boolean;
}

const VocabularyCallout = ({ vocabularyId, standardMode }: VocabularyCalloutProps) => {
  const term = displayTerm(vocabularyId, standardMode);

  return (
    <div className="rounded-lg border border-stone-200 bg-stone-50 p-3">
      <div className="text-sm font-semibold text-stone-900">{term.primary}</div>
      {term.secondary ? (
        <div className="mt-1 text-xs uppercase tracking-wide text-stone-500">
          {standardMode ? 'Repo aliases' : 'Standard label'}: {term.secondary}
        </div>
      ) : null}
    </div>
  );
};

const FiniteReptendDocument = () => {
  const [standardMode, setStandardMode] = useState(true);
  const exampleByN = new Map(canonicalExamples.map(example => [example.n, example]));

  const constantBridge = exampleByN.get(37);
  const primeBridge = exampleByN.get(97);
  const periodicCore = exampleByN.get(249);
  const compositePreperiod = exampleByN.get(996);
  const qrCounterexample = exampleByN.get(19);

  return (
    <div className="min-h-screen bg-stone-100 text-stone-800 selection:bg-stone-300">
      <div className="mx-auto max-w-6xl px-4 py-8 sm:px-6 sm:py-12">
        <header className="mb-8 rounded-sm border border-stone-200 bg-white p-5 shadow-sm sm:p-6">
          <div className="flex flex-col gap-5 lg:flex-row lg:items-end lg:justify-between">
            <div>
              <p className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
                Registry-Driven Reptends
              </p>
              <h1 className="mt-2 text-2xl font-serif font-semibold text-stone-900 sm:text-3xl">
                Exact identities first, visual language second
              </h1>
              <p className="mt-4 max-w-3xl text-sm leading-relaxed text-stone-700 sm:text-base">
                This site now treats the claim registry, counterexample registry,
                vocabulary table, and example atlas as the source of truth. The
                goal is not to sell novelty. It is to make the repo’s actual
                signal about reptends easy to inspect.
              </p>
            </div>
            <div className="rounded-sm border border-stone-200 bg-stone-50 p-4 text-sm text-stone-700">
              <div className="font-semibold text-stone-900">Current framing</div>
              <div className="mt-2">Classical number theory + formal proofs + curated examples</div>
              <div className="mt-1">Aliases remain available, but only after standard labels</div>
            </div>
          </div>
        </header>

        <section className="mb-8 grid gap-4 lg:grid-cols-[1.35fr_1fr]">
          <ClaimCard claimId="series_q_weighted_identity">
            <Block>
              1/N = q/(B-k) = (q/B) × 1/(1 - k/B) = Σ q k^j / B^(j+1)
            </Block>
          </ClaimCard>

          <aside className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm sm:p-5">
            <h2 className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500 mb-3">
              Standard Labels
            </h2>
            <div className="space-y-3">
              <VocabularyCallout vocabularyId="quotient_q" standardMode={standardMode} />
              <VocabularyCallout vocabularyId="remainder_k" standardMode={standardMode} />
              <VocabularyCallout vocabularyId="skeleton" standardMode={standardMode} />
              <VocabularyCallout vocabularyId="good_mode" standardMode={standardMode} />
            </div>
          </aside>
        </section>

        <section className="mb-8 rounded-sm border border-stone-200 bg-white p-4 shadow-sm sm:mb-10 sm:p-6">
          <h2 className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500 mb-3">
            Core Coordinate Story
          </h2>
          <p className="text-sm leading-relaxed text-stone-700 sm:text-base">
            A usable block coordinate starts when <M>B = base^m</M> exceeds the
            periodic modulus, so <M>q = (B-k)/N</M> is positive. In that
            coordinate, the raw coefficients are <M>qk^j</M>. When <M>q = 1</M>,
            the visible blocks really do reduce to literal powers of <M>k</M>.
          </p>
          <div className="mt-5 grid gap-4 md:grid-cols-2">
            <article className="rounded-lg border border-stone-200 bg-stone-50 p-4">
              <div className="flex items-center gap-2 mb-2">
                <div className="text-sm font-semibold text-stone-900">1/37</div>
                <code className="rounded bg-white px-2 py-1 text-xs text-stone-700">q = 27, k = 1</code>
              </div>
              <p className="text-sm leading-relaxed text-stone-700">
                {constantBridge?.explanation}
              </p>
            </article>
            <article className="rounded-lg border border-stone-200 bg-stone-50 p-4">
              <div className="flex items-center gap-2 mb-2">
                <div className="text-sm font-semibold text-stone-900">1/97</div>
                <code className="rounded bg-white px-2 py-1 text-xs text-stone-700">q = 1, k = 3</code>
              </div>
              <p className="text-sm leading-relaxed text-stone-700">
                {primeBridge?.explanation}
              </p>
            </article>
          </div>
        </section>

        <StandardTerminologyPanel
          standardMode={standardMode}
          onToggle={() => setStandardMode(value => !value)}
        />

        <ProofAtlasPanel />

        <CounterexampleRegistryPanel />

        <section className="mb-8 sm:mb-10">
          <div className="mb-5">
            <h2 className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500 mb-2">
              Prime, Composite, Carry
            </h2>
            <p className="text-sm sm:text-base leading-relaxed text-stone-700 font-serif">
              These sections are where the repo now has the most signal: exact
              stride classification on the prime side, CRT plus preperiod on the
              composite side, and an explicit carry transducer connecting raw
              coefficients to visible blocks.
            </p>
          </div>

          <div className="grid gap-4 lg:grid-cols-3">
            <ClaimCard claimId="qr_stride_classification">
              <div className="mt-4 rounded-lg border border-stone-200 bg-stone-50 p-3">
                <div className="text-xs font-bold uppercase tracking-wide text-stone-500 mb-2">
                  Canonical prime case
                </div>
                <p className="text-sm leading-relaxed text-stone-700">
                  {qrCounterexample?.explanation}
                </p>
                <div className="mt-3 text-xs text-stone-500">
                  Term in this section: {displayTerm('qr_generator', standardMode).primary}
                </div>
              </div>
            </ClaimCard>

            <div className="space-y-4">
              <ClaimCard claimId="crt_period_lcm">
                <div className="mt-4 text-sm leading-relaxed text-stone-700">
                  {periodicCore?.explanation}
                </div>
              </ClaimCard>
              <ClaimCard claimId="preperiod_from_base_factors">
                <div className="mt-4 text-sm leading-relaxed text-stone-700">
                  {compositePreperiod?.explanation}
                </div>
              </ClaimCard>
            </div>

            <ClaimCard claimId="carry_window_transducer">
              <div className="mt-4 grid gap-3">
                <VocabularyCallout vocabularyId="carry_layer" standardMode={standardMode} />
                <VocabularyCallout vocabularyId="body_term" standardMode={standardMode} />
                <VocabularyCallout vocabularyId="correction_term" standardMode={standardMode} />
              </div>
              <div className="mt-4 rounded-lg border border-amber-100 bg-amber-50 p-3 text-sm text-amber-900">
                Run <code>python -m bridge_reptends.examples.carry_transducer_demo</code> to
                see the raw coefficients, carry states, and visible blocks aligned
                on the same example.
              </div>
            </ClaimCard>
          </div>
        </section>

        <CuratedExamplesPanel standardMode={standardMode} />

        <section className="mb-8 sm:mb-10">
          <div className="mb-5">
            <h2 className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500 mb-2">
              Interactive Explorers
            </h2>
            <p className="text-sm sm:text-base leading-relaxed text-stone-700 font-serif">
              The interactives remain here as exploratory tools, not as theorem
              sources. Read them through the atlas and vocabulary tables above.
            </p>
          </div>

          <div className="mb-6 rounded-sm border border-stone-200 bg-white p-4 shadow-sm sm:p-6">
            <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-900 mb-3">
              {displayTerm('remainder_orbit', standardMode).primary}
            </h3>
            <p className="text-sm leading-relaxed text-stone-700 mb-4">
              The long-division remainder sequence can be read as a walk under
              multiplication by the base. This is the standard group-theoretic
              object behind the older “circle walk” language.
            </p>
            <CircleWalkPlayground />
          </div>

          <div className="grid gap-6 xl:grid-cols-2">
            <div className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm sm:p-6">
              <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-900 mb-3">
                {displayTerm('good_mode', standardMode).primary}
              </h3>
              <p className="text-sm leading-relaxed text-stone-700 mb-4">
                This explorer shows where the coordinate choice <M>B = base^m</M>
                makes the residue <M>k = B mod M</M> small enough to read.
              </p>
              <GoodCoordinatesExplorer />
            </div>

            <div className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm sm:p-6">
              <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-900 mb-3">
                Composite Core and Carry Overlay
              </h3>
              <p className="text-sm leading-relaxed text-stone-700 mb-4">
                This view ties together stripped moduli, preperiod, orbit length,
                and carry-normalized block output for composite denominators.
              </p>
              <OrbitCoreExplorer />
            </div>
          </div>
        </section>
      </div>
    </div>
  );
};

export default FiniteReptendDocument;
