import { M, Block, SectionDivider } from './shared';
import GoodCoordinatesExplorer from './GoodCoordinatesExplorer';
import OrbitCoreExplorer from './OrbitCoreExplorer';
import KFamilyExplorer from './KFamilyExplorer';
import StackVisualizer from './StackVisualizer';
import FluxContrast from './FluxContrast';
import CircleWalkPlayground from './CircleWalkPlayground';

const FiniteReptendDocument = () => {
  const powers = [5, 25, 125, 625, 3125, 15625, 78125, 390625, 1953125];
  const qrMod19 = [5, 6, 11, 17, 9, 7, 16, 4, 1];
  const chunks = [5, 26, 31, 57, 89, 47, 36, 84, 21];

  return (
    <div className="min-h-screen bg-stone-100 text-stone-800 font-sans selection:bg-stone-300">
      <div className="max-w-4xl mx-auto px-4 sm:px-6 py-8 sm:py-12">
        {/* Title & Abstract */}
        <header className="mb-8 sm:mb-10 border-b border-stone-300 pb-6">
          <h1 className="text-2xl sm:text-3xl font-serif font-semibold text-stone-900 mb-2">
            A Finite Formula for Reptends
          </h1>
          <p className="text-stone-600 text-sm sm:text-base font-serif italic">
            On the structure of repeating decimals as finite sums of powers
          </p>
          <p className="text-stone-500 text-xs mt-3 uppercase tracking-wider">
            M. & C. — December 2025
          </p>
        </header>

        <section className="mb-8 sm:mb-10 bg-white p-4 sm:p-6 rounded-sm shadow-sm border border-stone-200">
          <h2 className="text-xs font-bold text-stone-500 uppercase tracking-wide mb-3">
            Abstract
          </h2>
          <p className="text-stone-800 leading-relaxed font-serif text-sm sm:text-base">
            We show that the reptend of <M>1/19</M> can be written as a finite
            sum of nine powers of 5, plus a single correction term we call the{' '}
            <em>cyclic flux</em>. These two components telescope to recover the
            quotient <M>10¹⁸/19</M>, so the "infinite" decimal is encoded by
            finitely many powers and one boundary term. We then generalize this
            construction to a family of primes, revealing that the cyclic flux
            measures the cost of forcing a multiplicative orbit to live inside a
            fixed positional window.
          </p>
        </section>

        {/* Good Coordinates Explorer - the foundational framework */}
        <GoodCoordinatesExplorer />

        {/* Orbit Core Explorer - deep dive into orbit structure */}
        <OrbitCoreExplorer />

        {/* PART I */}
        <SectionDivider part="Part I" title="The Anatomy of 1/19" />

        {/* Section 1: Setup */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            1. Setup
          </h2>
          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            Consider the decimal expansion of <M>1/19</M>:
          </p>
          <Block>1/19 = 0.052631578947368421...</Block>
          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The reptend <M>R = 052631578947368421</M> has period 18 and
            satisfies <M>R = (10¹⁸ − 1)/19</M>. We can partition <M>R</M> into
            nine 2-digit chunks:
          </p>
          <div className="bg-stone-200 rounded px-4 py-3 font-mono text-xs sm:text-sm text-center mb-4 tracking-wider text-stone-700">
            05 | 26 | 31 | 57 | 89 | 47 | 36 | 84 | 21
          </div>
          <p className="text-stone-700 leading-relaxed text-sm sm:text-base">
            The number 9 is significant: it equals <M>(19−1)/2</M>, the count of
            quadratic residues mod 19, and also <M>ord₁₉(5)</M>, the
            multiplicative order of 5 mod 19. This is not a coincidence.
          </p>
        </section>

        {/* Section 2 */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            2. The Generator
          </h2>
          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            Since <M>100 ≡ 5 (mod 19)</M>, the value 5 serves as the 2-digit
            "word" generator. Its powers mod 19 cycle through exactly the nine
            quadratic residues:
          </p>
          <Block>5ⁱ mod 19: 5, 6, 11, 17, 9, 7, 16, 4, 1</Block>
          <div className="overflow-x-auto mb-4 border border-stone-200 rounded-lg shadow-sm">
            <table className="w-full text-xs sm:text-sm border-collapse bg-stone-50">
              <thead>
                <tr className="border-b border-stone-300 bg-stone-200">
                  <th className="py-2 px-3 sm:px-4 text-left font-bold text-stone-700 w-12 sm:w-16">
                    i
                  </th>
                  <th className="py-2 px-3 sm:px-4 text-left font-bold text-stone-700">
                    5ⁱ
                  </th>
                  <th className="py-2 px-3 sm:px-4 text-left font-bold text-stone-700">
                    5ⁱ mod 19
                  </th>
                  <th className="py-2 px-3 sm:px-4 text-left font-bold text-stone-700">
                    Chunk
                  </th>
                </tr>
              </thead>
              <tbody className="font-mono text-stone-700">
                {powers.map((p, i) => (
                  <tr
                    key={i}
                    className="border-b border-stone-200 hover:bg-stone-100 transition-colors"
                  >
                    <td className="py-2 px-3 sm:px-4 font-semibold text-stone-500">
                      {i + 1}
                    </td>
                    <td className="py-2 px-3 sm:px-4">{p.toLocaleString()}</td>
                    <td className="py-2 px-3 sm:px-4 text-stone-600">
                      {qrMod19[i]}
                    </td>
                    <td className="py-2 px-3 sm:px-4 font-bold text-stone-800">
                      {chunks[i].toString().padStart(2, '0')}
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </section>

        {/* Section 3 */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            3. The Direct Sum
          </h2>
          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            Place each power of 5 at its corresponding decimal position:
          </p>
          <Block>S = Σ(5ⁱ × 10¹⁸⁻²ⁱ) for i = 1 to 9</Block>
          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            Computing this sum gives <M>S = 52,631,578,947,265,625</M>. This is
            remarkably close to <M>R = 52,631,578,947,368,421</M>, but not
            exact:
          </p>
          <div className="bg-red-50 border-l-4 border-red-300 p-4 font-mono text-center text-red-800 mb-4 text-sm sm:text-base">
            R − S = 102,796
          </div>
          <p className="text-stone-700 leading-relaxed text-sm sm:text-base">
            Where does this gap come from? The visualization below shows the
            construction step by step.
          </p>
        </section>

        {/* VISUALIZATION: Stack Builder */}
        <StackVisualizer />

        {/* Section 4: The Cyclic Flux - EXPANDED */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            4. The Cyclic Flux
          </h2>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The "missing" 102,796 arises from the cyclic nature of the reptend.
            But before we derive the formula, we should pause to appreciate how
            strange this situation is.
          </p>

          <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-800 mt-6 mb-3">
            4.1 The Strangeness of Cyclic Carries
          </h3>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            In ordinary positional arithmetic, carries propagate leftward and
            eventually terminate. When you add 7 + 8 in the ones column, the
            carry goes to the tens column, and that's the end of it. The number
            line is linear; there's no wrap-around.
          </p>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            But a reptend is not linear. The decimal 0.052631578947368421...
            doesn't stop at digit 18—it continues with digit 1 again. The
            reptend lives on a <em>ring</em>, not a line. Position 17 (the
            leftmost) is topologically adjacent to position 0 (the rightmost),
            because after the 18th digit comes the 1st digit of the next cycle.
          </p>

          <div className="bg-amber-50 border border-amber-200 rounded-lg p-4 mb-4">
            <p className="text-amber-900 text-xs sm:text-sm">
              <strong>The unusual observation:</strong> We are doing arithmetic
              in a positional system (which is inherently linear) while
              representing a structure that is inherently cyclic. The flux is
              the price we pay for this mismatch.
            </p>
          </div>

          <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-800 mt-6 mb-3">
            4.2 Deriving the Formula
          </h3>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The direct sum S is a geometric series. Using the standard trick of
            multiplying by shifted copies and subtracting:
          </p>

          <div className="bg-stone-100 border border-stone-300 rounded-lg p-4 font-mono text-xs sm:text-sm mb-4">
            <div className="text-stone-800">100·S − 5·S = 5×10¹⁸ − 5¹⁰</div>
            <div className="text-stone-800 mt-1">95·S = 5×10¹⁸ − 5¹⁰</div>
            <div className="text-stone-900 font-bold mt-1">
              S = (5×10¹⁸ − 5¹⁰) / 95
            </div>
          </div>

          <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-800 mt-6 mb-3">
            4.3 The Bridge Number 95
          </h3>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The denominator 95 plays a crucial dual role:
          </p>

          <div className="bg-stone-200 rounded px-4 sm:px-6 py-4 mb-4 space-y-2 font-mono text-xs sm:text-sm border border-stone-300">
            <div className="flex flex-col sm:flex-row sm:items-center gap-1 sm:gap-4">
              <span className="font-bold text-stone-900">95 = 100 − 5</span>
              <span className="text-stone-500 italic text-[10px] sm:text-xs">
                (geometric-series denominator: B² − k)
              </span>
            </div>
            <div className="flex flex-col sm:flex-row sm:items-center gap-1 sm:gap-4">
              <span className="font-bold text-stone-900">95 = 19 × 5</span>
              <span className="text-stone-500 italic text-[10px] sm:text-xs">
                (prime × driver: p × k)
              </span>
            </div>
          </div>

          <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-800 mt-6 mb-3">
            4.4 Extracting the Flux
          </h3>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The geometric sum S is missing a "ghost term"—the contribution that
            would complete the pattern. To find it, we divide:
          </p>

          <Block>5⁹ / 19 = 102,796 + 1/19</Block>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            Why is the remainder exactly <M>1/19</M>? Because{' '}
            <strong>ord₁₉(5) = 9</strong>—the multiplicative order of 5 in
            (ℤ/19ℤ)* is 9. This means 5⁹ ≡ 1 (mod 19), so:
          </p>

          <div className="bg-stone-50 border border-stone-200 rounded-lg p-4 font-mono text-xs sm:text-sm mb-4">
            <div>5⁹ = 19 × 102,796 + 1</div>
            <div className="mt-2 text-stone-500">
              ↳ The orbit completes: 5⁹ lands back at 1
            </div>
          </div>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The integer part is our flux:
          </p>

          <Block>F = ⌊5⁹ / 19⌋ = 102,796</Block>

          <p className="text-stone-700 leading-relaxed bg-blue-50 p-4 rounded border-l-4 border-blue-300 text-sm sm:text-base">
            <strong>Self-reference:</strong> The fractional remainder is exactly{' '}
            <M>1/19</M>—the number whose reptend we're studying. This isn't
            coincidence: the remainder is 1/19 <em>because</em> the
            multiplicative orbit of 5 completes after 9 steps.
          </p>

          <p className="text-stone-600 text-xs sm:text-sm mt-4 italic">
            Note: We can also write this as 5¹⁰/95 since 95 = 19 × 5, but 5⁹/19
            is the fundamental form—it shows the orbit structure directly.
          </p>
        </section>

        {/* Section 5 */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            5. The Telescoping
          </h2>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The ghost term Q lets us see the telescoping clearly:
          </p>

          <div className="bg-stone-800 text-stone-100 rounded-lg p-4 sm:p-6 font-mono text-xs sm:text-sm space-y-2 mb-4 shadow-lg overflow-x-auto">
            <div>10¹⁸ / 19 = S + Q</div>
            <div className="pl-4 text-stone-400">
              = (5×10¹⁸ − 5¹⁰)/95 + 5¹⁰/95
            </div>
            <div className="pl-4 text-stone-300">
              = (5×10¹⁸ − 5¹⁰ + 5¹⁰) / 95
            </div>
            <div className="pl-4 text-stone-200">= 5×10¹⁸ / 95</div>
            <div className="pl-4 text-stone-100">= 5×10¹⁸ / (19 × 5)</div>
            <div className="pl-4 font-bold text-green-400">= 10¹⁸ / 19</div>
          </div>

          <p className="text-stone-700 leading-relaxed text-sm sm:text-base">
            Because Q = F + 1/19, we have{' '}
            <M>R = S + F = (10¹⁸ − 1)/19 = 52,631,578,947,368,421</M>.
          </p>
        </section>

        {/* Section 6 */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            6. The Fixed-Point View
          </h2>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The self-reference we found—where 1/19 appears inside the flux
            expression—suggests a reframing. The reptend is not "computed" digit
            by digit through long division. Instead, it is the unique periodic
            decimal satisfying a finite algebraic constraint.
          </p>

          <div className="bg-stone-200 rounded px-4 sm:px-6 py-4 mb-4 space-y-2 font-mono text-xs sm:text-sm border border-stone-300">
            <div className="flex flex-col sm:flex-row sm:items-center gap-1 sm:gap-4">
              <span className="w-8 font-bold text-stone-900">19</span>
              <span>= 2 × 10 − 1</span>
              <span className="text-stone-500 italic">(the prime)</span>
            </div>
            <div className="flex flex-col sm:flex-row sm:items-center gap-1 sm:gap-4">
              <span className="w-8 font-bold text-stone-900">5</span>
              <span>= 100 mod 19</span>
              <span className="text-stone-500 italic">(the generator)</span>
            </div>
            <div className="flex flex-col sm:flex-row sm:items-center gap-1 sm:gap-4">
              <span className="w-8 font-bold text-stone-900">95</span>
              <span>= 19 × 5 = 100 − 5</span>
              <span className="text-stone-500 italic">(the bridge)</span>
            </div>
          </div>

          <p className="text-stone-700 leading-relaxed text-sm sm:text-base">
            These three numbers encode the entire structure. The "infinite"
            decimal is actually the shadow of this finite configuration.
          </p>
        </section>

        {/* VISUALIZATION: Flux Contrast */}
        <FluxContrast />

        {/* PART II */}
        <SectionDivider
          part="Part II"
          title="From One Reptend to a General Theory"
        />

        {/* Section 7 */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            7. The Orbit-Stack Framework
          </h2>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The 1/19 construction generalizes. For any base B, prime p, driver
            k, and block size n, we can define:
          </p>

          <Block>L = ordₚ(B), R = (Bᴸ − 1)/p, k = Bⁿ mod p</Block>

          <p className="text-stone-700 leading-relaxed text-sm sm:text-base">
            The orbit of k mod p is the sequence [1, k, k², ...] until it
            returns to 1. When the period factorizes as L = n × ord (where ord =
            ordₚ(k)), one natural stack sum has the closed form{' '}
            <M>S = (Bᴸ − k^ord) / (Bⁿ − k)</M>.
          </p>
        </section>

        {/* Section 8 */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            8. Flux as Representation Cost
          </h2>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            With R and S defined, the flux F = R − S measures how expensive it
            is to force a multiplicative orbit into a positional window:
          </p>

          <ul className="list-disc list-inside text-stone-700 leading-relaxed space-y-2 mb-4 ml-4 text-sm sm:text-base">
            <li>
              <strong>F {'>'} 0:</strong> The stack is sparse. Terms spread out;
              flux tops up the gap.
            </li>
            <li>
              <strong>F {'<'} 0:</strong> The stack is dense. Terms collide;
              carries compress; flux corrects downward.
            </li>
          </ul>

          <p className="text-stone-700 leading-relaxed text-sm sm:text-base">
            The ratio |F/R| serves as a quality score: smaller values indicate
            better "fit" between the multiplicative structure and the positional
            representation.
          </p>
        </section>

        {/* Section 9 */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            9. Examples and Patterns
          </h2>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The bridge pattern recurs for primes near powers of 10:
          </p>

          <div className="overflow-x-auto mb-4 border border-stone-200 rounded-lg shadow-sm">
            <table className="w-full text-xs sm:text-sm border-collapse bg-stone-50">
              <thead>
                <tr className="border-b border-stone-300 bg-stone-200">
                  <th className="py-2 px-3 sm:px-4 text-left font-bold text-stone-700">
                    p
                  </th>
                  <th className="py-2 px-3 sm:px-4 text-left font-bold text-stone-700">
                    Bridge Equation
                  </th>
                  <th className="py-2 px-3 sm:px-4 text-left font-bold text-stone-700">
                    1/p =
                  </th>
                  <th className="py-2 px-3 sm:px-4 text-left font-bold text-stone-700">
                    Period
                  </th>
                  <th className="py-2 px-3 sm:px-4 text-left font-bold text-stone-700">
                    Chunks
                  </th>
                </tr>
              </thead>
              <tbody className="font-mono text-stone-700">
                <tr className="border-b border-stone-200 hover:bg-stone-100">
                  <td className="py-2 px-3 sm:px-4 font-bold text-stone-800">
                    19
                  </td>
                  <td className="py-2 px-3 sm:px-4">100 = 5·19 + 5</td>
                  <td className="py-2 px-3 sm:px-4">5/(100 − 5)</td>
                  <td className="py-2 px-3 sm:px-4">18</td>
                  <td className="py-2 px-3 sm:px-4">9</td>
                </tr>
                <tr className="border-b border-stone-200 hover:bg-stone-100">
                  <td className="py-2 px-3 sm:px-4 font-bold text-stone-800">
                    97
                  </td>
                  <td className="py-2 px-3 sm:px-4">100 = 1·97 + 3</td>
                  <td className="py-2 px-3 sm:px-4">1/(100 − 3)</td>
                  <td className="py-2 px-3 sm:px-4">96</td>
                  <td className="py-2 px-3 sm:px-4">48</td>
                </tr>
                <tr className="border-b border-stone-200 hover:bg-stone-100">
                  <td className="py-2 px-3 sm:px-4 font-bold text-stone-800">
                    199
                  </td>
                  <td className="py-2 px-3 sm:px-4">1000 = 5·199 + 5</td>
                  <td className="py-2 px-3 sm:px-4">5/(1000 − 5)</td>
                  <td className="py-2 px-3 sm:px-4">99</td>
                  <td className="py-2 px-3 sm:px-4">33</td>
                </tr>
                <tr className="border-b border-stone-200 hover:bg-stone-100">
                  <td className="py-2 px-3 sm:px-4 font-bold text-stone-800">
                    9997
                  </td>
                  <td className="py-2 px-3 sm:px-4">10000 = 1·9997 + 3</td>
                  <td className="py-2 px-3 sm:px-4">1/(10000 − 3)</td>
                  <td className="py-2 px-3 sm:px-4">192</td>
                  <td className="py-2 px-3 sm:px-4">48</td>
                </tr>
              </tbody>
            </table>
          </div>
        </section>

        {/* Interactive Explorer */}
        <KFamilyExplorer />

        {/* Section 10 */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            10. Concluding Remarks
          </h2>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The "infinite" repeating decimal of 1/19 encodes finite data: nine
            powers of the generator 5, plus one boundary term tied to the bridge
            95. The flux measures the gap between a multiplicative orbit (which
            wants to live in a cyclic group) and a positional representation
            (which forces it into a linear window).
          </p>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            More broadly, every repeating decimal is a projection: a
            multiplicative structure forced into an additive costume. The
            Orbit-Stack framework makes this tension precise and measurable.
          </p>

          <p className="text-stone-700 leading-relaxed text-sm sm:text-base">
            What looks like endless recurrence is the shadow of a finite
            geometric construction. Numbers don't want to be decimals. They want
            to be orbits.
          </p>
        </section>

        <SectionDivider part="Part III" title="The Geometric View" />

        {/* Section 11: The Point and the Path */}
        <section className="mb-8 sm:mb-10">
          <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-4">
            11. The Point and the Path
          </h2>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            A fraction like <M>1/19</M> isn't an infinite decimal—it's a{' '}
            <strong>position on a circle</strong>. The circle has 18 points (one
            for each non-zero residue mod 19). Your starting point is 1.
          </p>

          <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
            The <strong>base</strong> is how you walk. When you "compute" the
            decimal in base 10, you're stepping around the circle with step size
            10. Each step: multiply your position by the base, wrap around (mod
            p), and the overflow becomes a digit.
          </p>

          <p className="text-stone-700 leading-relaxed mb-6 text-sm sm:text-base">
            Different bases give <strong>different walks</strong>. Same circle,
            same starting point, different tours. Try switching from base 10 to
            base 7 below—watch the path change, the digits change, but the
            structure remains. The "infinite" repetition? It's just the finite
            orbit, looped forever. The snake eating its tail.
          </p>

          <CircleWalkPlayground />

          <p className="text-stone-600 text-xs sm:text-sm mt-6 italic text-center">
            The number is the point. The decimal is the path you trace.
          </p>
        </section>

        {/* Verification */}
        <section className="border-t border-stone-300 pt-6 sm:pt-8 mt-10 sm:mt-12">
          <h2 className="text-xs font-bold text-stone-400 uppercase tracking-widest mb-4">
            Numerical Verification
          </h2>

          <div className="bg-stone-100 border border-stone-200 rounded-lg p-4 sm:p-6 font-mono text-xs sm:text-sm space-y-2">
            <div className="flex justify-between text-stone-600">
              <span>Direct sum S</span>
              <span>52,631,578,947,265,625</span>
            </div>
            <div className="flex justify-between text-stone-600">
              <span>Cyclic flux F</span>
              <span>+ 102,796</span>
            </div>
            <div className="border-t border-stone-300 pt-2 mt-2 flex justify-between font-bold text-stone-800">
              <span>R = S + F</span>
              <span>52,631,578,947,368,421</span>
            </div>
            <div className="text-green-600 text-xs mt-3 text-right flex items-center justify-end gap-2">
              <span className="inline-block w-2 h-2 rounded-full bg-green-500"></span>
              Matches (10¹⁸ − 1) / 19
            </div>
          </div>

          <div className="bg-stone-100 border border-stone-200 rounded-lg p-4 sm:p-6 font-mono text-xs sm:text-sm mt-4">
            <div className="text-stone-600 mb-2">Self-reference check:</div>
            <div className="text-stone-700">
              5¹⁰ / 95 = 9,765,625 / 95
            </div>
            <div className="text-stone-700 pl-4 sm:pl-8">
              = 102,796.052631578947368421...
            </div>
            <div className="text-green-600 text-xs mt-2 flex items-center gap-2">
              <span className="inline-block w-2 h-2 rounded-full bg-green-500"></span>
              Fractional part equals 1/19 (the exponent 10 = ord + 1 = 9 + 1)
            </div>
          </div>
        </section>

        {/* Footer */}
        <footer className="mt-12 sm:mt-16 pt-6 sm:pt-8 border-t border-stone-200 text-center text-stone-400 text-xs font-serif">
          <p className="italic mb-2">
            "Numbers don't want to be decimals. They want to be orbits."
          </p>
          <p>Collaborative work — M. & C. — December 2025</p>
        </footer>
      </div>
    </div>
  );
};

export default FiniteReptendDocument;
