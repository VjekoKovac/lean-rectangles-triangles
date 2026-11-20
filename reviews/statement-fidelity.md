# Independent AI review of the four source statements

The reviewer is a separate AI agent. It read the introduction and proofs before inspecting the Lean definitions. No human sign-off is claimed. The numbers below are the printed theorem numbers. Item 1.1 is a question.

**Source.** Jonathan Bennett, Vjekoslav Kovač, Shohei Nakamura, and Itamar Oliveira, *Rectangles, triangles and Schrödinger waves*, arXiv:2606.30178v1, 29 June 2026. I compared the four displays on printed pages 3, 8, and 9 of the [versioned PDF](https://pdfs.assets.alphaxiv.org/2606.30178v1.pdf) with the uploaded TeX. The hypotheses, quantified variables, comparisons, and exponents agree. This comparison covers the four source statements. It does not assert byte identity of the two complete manuscripts.

## What the constants measure

Write R and Rpin for the configuration ratios in Theorem 1.2. For nonempty finite A in the integer plane, the common numerator counts ordered (a,b,c,e) in A⁴ with a+c=b+e and (b−a)·(e−a)=0. For an apex k in A, T(k) counts ordered (a,b) in A² such that (2k−a−b)·(b−a)=0. The two denominators are the sum of T(k) over A and |A| times the maximum of T(k) over A. Equal vertices are included. In particular, T(k)≥|A|. With a radius bound, each ratio is maximized over nonempty sets in the closed coordinate cube. With a cardinality bound, take the supremum over sets of exactly the indicated size anywhere in the lattice.

Write S and M for the Stein and Mizohata–Takeuchi best constants in the paper. Periodic data are finitely supported complex Fourier coefficients a(k). The spatial and temporal variables have normalized Haar measure on the unit tori. Each term has spatial frequency k and temporal frequency |k|². The tested rays have spatial position x−2tk. Weights are nonnegative locally integrable functions. The periodic numerator integrates |u|²w over one spacetime period. For each k, the ray maximum is the pointwise supremum over x of the one-period integral of w along the ray. S weights the separate ray maxima by |a(k)|² and sums them. M multiplies the total coefficient energy by the largest ray maximum on the actual frequency support.

In Euclidean space, replace the finite sum by the Fourier extension integral of a square-integrable profile F, band-limited in the closed cube. The temporal interval in the numerator is [0,1]. The Euclidean ray integrates over the entire real time axis. The two denominators are the frequency integrals of |F|² times the respective velocity-dependent or support-wide ray maxima. These definitions use the positive sign in the exponential. Unit period, the factor 2 in the velocity, and the energy normalization matter for the exact inequalities.

## Four assertions

| Printed result | Quantifiers and conclusion | Proof detail that prevents an accidental weakening |
| --- | --- | --- |
| 1.2, p. 3 | A single absolute c>0 works for all sufficiently large real radii N and all sufficiently large positive integers n. In each family the unpinned extremum dominates the pinned extremum, which dominates (log x)^(c/log(log(log x))). | A family at selected radii or cardinalities is insufficient. Section 2.3 interpolates between adjacent lifted lattice sets to obtain every large exact n. |
| 1.3, p. 8 | For each integer d≥1 and real N≥1, each periodic constant at N is at most the corresponding Euclidean constant at N+1. | The coefficient in each comparison is exactly 1. Section 3.1 uses disjoint packets with normalized mass and passes to a limit. Section 3.2 gives a distinct qualitative converse. |
| 1.4, p. 8 | For every real N≥1 and every integer n≥1 in dimension 2, the box and exact-cardinality Stein constants dominate the respective unpinned ratios. The analogous two M constants dominate the pinned ratios. | These four inequalities have coefficient 1. The weight is the square modulus of the wave with all coefficients equal to 1 on A. The origin attains the spatial ray maximum. |
| 1.5, p. 9 | For every integer d≥1, each periodic constant is bounded below by c_d(log N)^d for all sufficiently large real N. Each exact-cardinality constant lies between c′_d n and C_d n for every sufficiently large positive integer n, with all multiplicative constants finite and positive. | A lower bound on both cardinality constants alone misses half the assertion. Section 5 uses unequal block sizes to realize exact n and a separate Cauchy–Schwarz / Haar-translation argument for the upper bound. |

## Formal conventions reviewed

In `RTS/Combinatorics.lean`, `sSup` over sets inside a fixed box has the same mathematical meaning as the printed maximum, since there are finitely many lattice points in a bounded box. Positivity of denominators follows from the allowed repeated vertices. The box radius is real, each coordinate uses an absolute-value bound, and the size constraint is equality. Writing the two order comparisons with ≤ and reversed operands preserves the displays.

In `RTS/AnalysisDefs.lean`, the finitely supported map removes zero coefficients from its support. Frequency profiles are a Plancherel parametrization of Euclidean initial data. The support of the measure with density ‖F‖² is the essential closed support. This convention makes the support intrinsic to L² initial data. Pointwise representatives are retained for weights because a single X-ray can intersect a spacetime-null set in positive time measure. The code uses nonnegative lower integrals for the corresponding pointwise line integrals, including extended values. For measurable line restrictions these are the usual nonnegative integrals. The eligibility conditions on weights require product-measure integrability or local integrability. These do not ensure measurability on every individual line. The lower-integral convention gives a meaning on exceptional lines where a literal Lebesgue integral would be undefined. Equivalence of alternative conventions for such lines is not claimed as a separately proved Lean lemma.

The constants are infima in the complete lattice of extended nonnegative reals. This avoids assigning an arbitrary real number to an unbounded supremum or an empty set of finite admissible constants. Numerical asymptotic constants and thresholds in Theorem 1.5 must still be real, or finite when represented as extended values. Pointwise dominance of the separate Stein denominator by the MT denominator yields the reverse comparison of the best constants.

## Review of the frozen challenge

I read the complete standalone `Challenge.lean`, including its definitions, against the source checklist above. It imports only public mathlib modules. The four terminal declarations quantify over the intended objects without adding analytic inequalities, construction witnesses, proof certificates, or other results as assumptions. The definition of `TrigonometricGrowth` includes both cardinality upper bounds. Its real constants and thresholds are scoped inside the dimension quantifier and outside the scale quantifiers. The sharp inequalities use comparisons in ℝ≥0∞, while the numerical side of each lower bound is explicitly included via `ENNReal.ofReal`. Using common positive constants for the two estimates in a family is equivalent to taking minima of positive lower constants and maxima of upper constants.

For the Fourier sign and period, I also inspected `fourier_coe_apply` in the pinned mathlib. It evaluates the character at a real representative as exp(2πinx/T). For the combinatorial definitions I kernel-checked an asymmetric three-point sample directly against the project API in `reviews/OrderedCounts.lean`. It has 15 ordered rectangles and 11 triangles. Its pinned counts are 5, 3, and 3, giving pinned denominator 15.

**Reviewed SHA-256**

- `Challenge.lean` — `db018a3683f8851e4650e65c1ec458bddf7b5dfb99f2b709974400c25d9a3e39`
- Uploaded TeX — `a0b37ca6006ff2dcf0e75f4cd6cdcc6bfe0552f829a70ecce05d7703009a58e9`

The four challenge declarations have intentional proof holes. Statement review gives no evidence for inhabitation of these propositions. Certification requires the separate solution proof and the comparator run for that declaration.

## Comparison with the four solution declarations

I inspected the final four named theorem types and their proof terms in `Solution.lean`. They respectively target `CombinatorialGrowth`, `QuantitativeTransference`, `ConfigurationLowerBounds`, and `TrigonometricGrowth`, with no added arguments. I also followed these proposition definitions in the implementation modules and in the standalone challenge. The source comparisons in the table above hold for both copies. Every solution term calls a proof of its corresponding predicate. The solution imports proof modules independently of the challenge. The reviewed `Solution.lean` file has SHA-256 `628dfdf992c90ce36cdbb9c548de2a48ca5d548a1837e252bf23a4b62a3b013b`. The mechanical test of agreement of the elaborated declarations is reported by Lean Comparator.
