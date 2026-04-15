interface GuideCard {
  title: string;
  summary: string;
  paths: string[];
  commands: string[];
}

const guideCards: GuideCard[] = [
  {
    title: 'Throughline Thesis',
    summary:
      'Start here if you want the repo-level spine: orbit layer, raw qk^j layer, carry normalization, and the open factorization frontier.',
    paths: [
      'README.md',
      'docs/EXPOSITORY_NOTE.md',
      'bridge_reptends/examples/orbit_plus_carry_tour.py',
    ],
    commands: [
      'python -m bridge_reptends.examples.orbit_plus_carry_tour',
      'search-reptends orbit-carry-frontier --max 1200 --base 10 --blocks 8',
    ],
  },
  {
    title: 'Claim Atlas',
    summary:
      'Use this when you want to separate theorem-level support from implemented, empirical, and open layers before reading the visuals too literally.',
    paths: [
      'docs/PROOF_STATUS_ATLAS.md',
      'docs/THEOREM_WITNESS_ATLAS.md',
      'data/claim_registry.json',
    ],
    commands: [
      'search-reptends theorem-witnesses --claim incoming_carry_position_formula',
      'python -m bridge_reptends.sync_registry_docs --check',
    ],
  },
  {
    title: 'State-Merging Atlas',
    summary:
      'This is the current frontier surface for finite-window compression, visible vs hidden obstruction, and same-core family drift.',
    paths: [
      'docs/CARRY_TRANSDUCER.md',
      'bridge_reptends/transducer.py',
      'lean/QRTour/Factorization.lean',
    ],
    commands: [
      'python -m bridge_reptends.examples.state_merging_tour',
      'python -m bridge_reptends.examples.quotient_obstruction_tour',
      'search-reptends state-merging --max 500 --base 10 --blocks 8',
    ],
  },
  {
    title: 'Linked 97 Coordinate Views',
    summary:
      'These are the best terminal entry points for the linked orbit, carry, and visible-block story behind the 1/97 panels.',
    paths: [
      'bridge_reptends/examples/carry_transducer_demo.py',
      'bridge_reptends/examples/orbit_plus_carry_tour.py',
      'bridge_reptends/transducer.py',
    ],
    commands: [
      'python -m bridge_reptends.examples.carry_transducer_demo',
      "python -c \"from bridge_reptends import print_skeleton_analysis; print_skeleton_analysis(97)\"",
    ],
  },
  {
    title: 'Prime Family Sweep',
    summary:
      'This is the best place to see whether a nice example is special or just photogenic. The companion script prints the B = 100 sweep directly in the terminal.',
    paths: [
      'bridge_reptends/examples/prime_family_sweep_100.py',
      'bridge_reptends/visibility.py',
      'site/src/components/PrimeFamilySweep100.tsx',
    ],
    commands: [
      'python -m bridge_reptends.examples.prime_family_sweep_100',
      'search-reptends small-residue-coordinates-q1 --max 1500 --top 10',
    ],
  },
  {
    title: 'Roots-of-Unity Geometry',
    summary:
      'When you want the orbit layer as actual cyclic geometry, these are the best follow-up files and scripts to read.',
    paths: [
      'bridge_reptends/examples/prime_19.py',
      'bridge_reptends/examples/progression.py',
      'lean/QRTour/QuadraticResidues.lean',
    ],
    commands: [
      'python -m bridge_reptends.examples.prime_19',
      'python -m bridge_reptends.examples.progression',
      "python -c \"from bridge_reptends import analyze_prime; print(analyze_prime(97))\"",
    ],
  },
];

const CoreSurfaceGuidePanel = () => {
  return (
    <section className="mb-8 sm:mb-10">
      <div className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm sm:p-6">
        <div className="grid gap-6 xl:grid-cols-[0.95fr_1.05fr]">
          <div>
            <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
              Where To Look Next
            </div>
            <h2 className="mt-2 text-xl font-serif font-semibold text-stone-900 sm:text-2xl">
              Repo entry points behind the core surfaces
            </h2>
            <p className="mt-3 max-w-3xl text-sm leading-relaxed text-stone-700 sm:text-base">
              The strongest panels on the page now point back into a small set of
              docs, formal modules, example scripts, and search surfaces. This
              section is the short map for curious readers who want more than the
              visual layer.
            </p>
            <div className="mt-4 rounded-lg border border-stone-200 bg-stone-50 p-4 text-sm leading-relaxed text-stone-700">
              <div className="font-semibold text-stone-900">Best first terminal path</div>
              <p className="mt-2">
                Start with the throughline tour, then the state-merging tour,
                then the B = 100 prime sweep if you want a landscape check.
              </p>
              <div className="mt-3 space-y-2">
                <code className="block rounded bg-white px-3 py-2 text-xs text-stone-600">
                  python -m bridge_reptends.examples.orbit_plus_carry_tour
                </code>
                <code className="block rounded bg-white px-3 py-2 text-xs text-stone-600">
                  python -m bridge_reptends.examples.state_merging_tour
                </code>
                <code className="block rounded bg-white px-3 py-2 text-xs text-stone-600">
                  python -m bridge_reptends.examples.prime_family_sweep_100
                </code>
              </div>
            </div>
          </div>

          <div className="grid gap-4 md:grid-cols-2">
            {guideCards.map(card => (
              <article
                key={card.title}
                className="rounded-lg border border-stone-200 bg-stone-50 p-4"
              >
                <h3 className="text-base font-serif font-semibold text-stone-900">
                  {card.title}
                </h3>
                <p className="mt-2 text-sm leading-relaxed text-stone-700">
                  {card.summary}
                </p>

                <div className="mt-4 text-[11px] font-bold uppercase tracking-[0.16em] text-stone-500">
                  Look In Repo
                </div>
                <div className="mt-2 space-y-2">
                  {card.paths.map(path => (
                    <code
                      key={`${card.title}-${path}`}
                      className="block rounded bg-white px-3 py-2 text-xs text-stone-600"
                    >
                      {path}
                    </code>
                  ))}
                </div>

                <div className="mt-4 text-[11px] font-bold uppercase tracking-[0.16em] text-stone-500">
                  Try In Terminal
                </div>
                <div className="mt-2 space-y-2">
                  {card.commands.map(command => (
                    <code
                      key={`${card.title}-${command}`}
                      className="block rounded bg-white px-3 py-2 text-xs text-stone-600"
                    >
                      {command}
                    </code>
                  ))}
                </div>
              </article>
            ))}
          </div>
        </div>
      </div>
    </section>
  );
};

export default CoreSurfaceGuidePanel;
