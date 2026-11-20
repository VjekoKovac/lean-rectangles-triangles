# Independent AI review of the proofs

The reviewer inspected the proof files separately from their authors. The outcome of Lean elaboration, the axiom traversal, and the external kernel runs must be read from their individual logs. This document records the mathematical audit.

## Theorem 1.4

The solution declaration `RTS.configuration_lower_bounds` delegates to `RTS.Configuration.configurationLowerBounds`. I traced its four branches back to the definitions of the wave, best constants, and ordered counts.

1. `configCoeff` is the indicator of the finite frequency set. Its support is exactly that set. The chosen weight is the squared modulus of this particular wave. Its nonnegativity and integrability are proved from continuity on the compact spacetime torus.
2. Multiplying the wave by itself selects two positive frequencies. In the squared norm of that product, independent positive and negative pairs survive exactly when their spatial frequency sums and energies agree. By the parallelogram identity the energy condition is twice the dot product of adjacent sides. It remains valid if one or both sides have zero length. This proves `rectangle_integral`.
3. On a ray, a mode has temporal frequency |a|²−2a·k. Equality with the temporal frequency for b is the triangle predicate with apex k. Every surviving phase has modulus one and all phases equal one at the origin. The bound at each intercept, `pinned_integral_le`, suffices for the main theorem. `pinned_integral_at_zero` checks sharpness.
4. Every admissible Stein constant bounds the quotient using the sum of the apex counts. Every admissible MT constant bounds the corresponding quotient using the maximum. The helper lemmas have moment and ray hypotheses. Every application in `ConfigurationProof.lean` supplies the previous unconditional proofs of these hypotheses. The code takes the infimum over admissible constants and bounds the supremum over the eligible finite sets. It does not need a minimizer for the admissible constant.
5. The exact-size cases use equality of support cardinality to n. In the box cases the code verifies membership frequency by frequency. These statements also follow for a few degenerate inputs outside the paper's ranges due to conventions on empty sets, but the challenge asserts only its stated domains.

## Reproducible numerical checks

The reviewer wrote the three checks below independently of the solution proofs. Each was accepted with `by decide` under Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The printed transitive axiom sets are all `[propext, Classical.choice, Quot.sound]`. Commands and output appear in `evidence/ordered-counts.txt`, `evidence/prime-three.txt`, and `evidence/two-block.txt`.

| Check | Input | Verified output |
| --- | --- | --- |
| `reviews/OrderedCounts.lean`, using the project's geometric definitions | Three vertices of the unit square | 15 rectangles, 11 triangles, individual apex counts 5, 3, 3, pinned denominator 15. |
| `reviews/PrimeThree.lean`, independent enumeration | The unit circle in the plane over the field with three elements | 4 points, 96 parametrized rectangles, 72 parametrized triangles, and 18 parametrized triangles at every apex. |
| `reviews/TwoBlock.lean`, independent enumeration | Disjoint dyadic blocks of lengths 3 and 2, choosing one element in each block | 6 frequencies, exactly 6 ordered temporal coincidences at each of the 6 tested slopes, and 90 spacetime frequency coincidences versus the claimed lower bound of 48. |

The finite tests validate normalization, degeneracies, and specific arithmetic cases. None proves a general growth or transference assertion.

## Theorem 1.5 proof source

I independently followed the chain of the `RTS.Dyadic.trigonometricGrowth` proof through `Weights.lean`.

- The frequency and subset families use disjoint exponent blocks of lengths mₗ. The data have one nonzero coefficient at each of exactly ∏ₗ mₗ frequencies. The auxiliary polynomial is specified separately, and the weight is its squared modulus.
- At a tested velocity, the nonexceptional terms in the difference of two subset frequencies have distinct 2-adic orders. A term of minimal order cannot cancel. After these coefficients vanish, equal subset cardinality in each coordinate forces the exceptional coefficient to vanish as well. This proves injectivity of the projected temporal frequencies. Orthogonality gives the exact X-ray mass used by the denominator.
- The collision proof counts pairs of terms of the product polynomial. A tuple of subsets of cardinalities rₗ+1, together with two independent marked elements in each coordinate, encodes a collision. Reinserting the first marked vector recovers the original subsets, and both marks can be read off the two terms. Thus the map counts distinct ordered collisions. Additional accidental Fourier coincidences can only increase the numerator. This proves the same lower bound as the source without requiring an exact formula for the numerator.
- The quotient uses only sets with positive mₗ, so the coefficient energy and the binomial denominator are positive. For equal lengths, the flooring argument works at every large real radius N. Its lower constant can be chosen as (8d log 2)^(−d). One length n together with d−1 lengths equal to 1 gives exact support n and the explicit lower bound n/4 in every dimension d≥1.
- The upper bound for every eligible datum uses pointwise Cauchy–Schwarz and the average X-ray identity proved by measure-preserving torus translation. The MT denominator dominates the Stein denominator, hence MT ≤ Stein. Only the MT lower bound and Stein upper bound require separate proofs. Their proved order gives the other two comparisons. The top-level proof discharges the numerator and denominator premises of `test_to_lower`.

## Additional proof authorship

After completing the independent statement audit and the audits of Theorems 1.4 and 1.5, this reviewer contributed the continuous-kernel approximation in `RTS/WeightApproximation.lean`, the uniform-count interface in `RTS/LiftingBounds.lean`, the exact-cardinality interpolation and growth reduction in `RTS/LiftingInterpolation.lean`, and repairs to the parameter-set membership proofs and the lower bound for rectangle origins in `RTS/LiftingTuples.lean`. Those contributions are AI-authored proof development. They require separate review and are outside the independent proof-audit claims above.

## Theorem 1.3 proof audit

I traced `quantitative_transference` to `periodic_le_euclidean`, which considers every Euclidean admissible constant C. The case C = ∞ follows by order. For finite C, the proof transfers its inequality and takes the infimum. In particular, it assumes neither attainment of an extremum nor validity of either global conjecture.

- The Euclidean datum uses compact frequency boxes centered at integer frequencies. Indicator packets of positive side length r replace the paper's Schwartz-profile packets. These are eligible square-integrable Fourier data. For 0<r<1/2 the supports are disjoint, and for r≤1 they lie in the cube with radius N+1. Indicator boundaries have zero frequency volume. No continuity of the frequency indicator is needed.
- Spatial tiling and Parseval turn the weighted Euclidean numerator into an average of a shifted finite periodic wave. The profile energy is exactly rᵈ times the total discrete coefficient energy. The same factor multiplies the estimated numerator and denominator. `continuous_transfer` proves that this factor is strictly positive and finite before cancelling it.
- `liftedWeight` truncates the periodic representative to one real time period. Consequently, its real-time X-ray is the intended periodic time average even though the Euclidean X-ray generally integrates over all times. The limit of the Stein expression is a weighted sum of separate ray maxima. The MT branch uses a maximum on the thickened support and explicitly handles empty Fourier support.
- The convolved weights have ray maxima no larger than those of the original measurable weight. For product-a.e. measurable representatives, the proof first constructs a measurable minorant agreeing almost everywhere. The numerator is unchanged and every pointwise ray denominator can only decrease. This use of an actual minorant matters because equality almost everywhere in spacetime alone need not preserve a chosen line integral.
- The final two applications specialize the same proved transfer to Stein and MT. I audited the preceding organization and estimates independently. My own contribution within the measurable-weight reduction is identified above.

## Theorem 1.2 proof audit

I checked the organization of the finite-field, congruence, and lattice parts separately from the reviewers' contributions to interpolation.

- The unit circle has p+1 points for a prime p congruent to 3 modulo 4. The rotation to coordinates based at a circle point preserves the quadratic form and the quarter turn. The counts use the tuple (x,w,r,s), with w nonzero and with zero scalars permitted. The resulting factor 4/3 per prime is a ratio between these parametrized counts. The concrete three-element-field enumeration in this folder independently checks these conventions.
- The CRT stage uses a finite set of distinct primes. Each allowed direction is nonzero in every local plane. Point membership and the base/apex conditions are transferred along actual equivalences. This distinguishes the required direction condition from the weaker condition that a single vector over the composite ring be nonzero.
- The lattice stage lifts modular residues and counts integer perpendicular sides as primitive directions and scalar multiples of their quarter turns. It bounds the rectangle multiplicity by two and adds one for the entirely degenerate pinned configuration. The source's ordered repeated-vertex cases are retained.
- In the quantitative sieve, the reciprocal-square sum over nonprimitive multiples is bounded using an explicit summable tail. The formal proof needs an absolute positive leading lower coefficient and a matching-order upper coefficient. It therefore uses direct bounds in place of evaluating the exact Euler-product coefficient of the auxiliary asymptotic. Rectangle directions are sampled in a smaller box to make the integer scalar choices uniformly numerous. These changes affect absolute constants in internal bounds, which the theorem leaves unspecified.
- Quantitative distribution of primes supplies a product no larger than exp(Dm log m). The final choice of m gives a shared exponent at both kinds of scale. The exact-size step encloses an n-point set between two adjacent integer boxes. The numerator is bounded from below in the smaller box, and the whole pinned denominator from above in the larger one. It only uses monotonicity of individual counts. Monotonicity of the ratio under inclusion would not justify this step.

`RTS.combinatorialGrowth` takes D from the quantitative prime-product theorem, builds a CRT prime set of precisely m elements, and supplies `fixed_modulus_bound` to the growth reduction. I checked the origins of all three absolute constants in its final application. The threshold coefficient 1000 controls the sieve errors. The factor 1/1024 gives a lower bound for the rectangle tuple count and is halved for the passage to geometric rectangles. The pinned coefficient 10000 and the circle-size upper bound 9 produce the denominator 9(10000+1). Thus the coefficient multiplying (4/3)^m is a fixed positive real. The combinatorial interpolation proof then absorbs fixed losses by reducing a single exponent c used for both conclusions.

A second AI reviewer who authored the circle-lift module reviewed the interpolation separately. They confirmed that the least crossing radius handles equal cardinalities at successive radii, that the pinned denominator is positive, that the loss from adjacent scales is at most 32 for t≥2, and that the continuous box radius argument includes every real N beyond the fixed threshold.
