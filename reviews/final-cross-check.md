# Additional independent AI review

This review was performed by a separate AI agent that wrote none of the project’s Lean modules. I compared the four public declarations and their definitions with the four numbered theorem displays in the [arXiv source](https://arxiv.org/abs/2606.30178v1). I then traced the specific issues below in the proof sources. The standalone challenge I read has SHA-256 `db018a3683f8851e4650e65c1ec458bddf7b5dfb99f2b709974400c25d9a3e39`.

| Issue | What the proof establishes |
|---|---|
| Distribution of primes in Theorem 1.2 | The imported `chebyshev_asymptotic_pnt` concerns the **prime** sum weighted by `log p`. Its hypotheses at residue 3 modulo 4 are `4 ≥ 1`, `3.Coprime 4`, and `3 < 4`. The relative asymptotic gives a lower bound on the weighted sum at x = m². Dividing by the largest possible log p gives at least m primes eventually. Taking a larger fixed cutoff deals with all smaller m ≥ 2. Selecting exactly m of these primes gives a real D independent of m, with product at most exp(Dm log m). This supplies the same modulus-size control as selecting the first m primes in the paper. |
| Fixed modulus and exact-size interpolation in Theorem 1.2 | In `LiftingAssembly.lean` the common scale coefficient is positive. The modular gain survives cancellation as (4/3) raised to the actual cardinality of the prime set. The entirely degenerate pinned triangle is accounted for by an additive one. At exact size n, `LiftingInterpolation.lean` chooses a set between adjacent boxes using monotonicity of counts. The upper bound on the pinned denominator comes from the larger set and the rectangle lower bound from the smaller one. The factor 32 is absolute. `GrowthReduction.lean` chooses the logarithmic exponent once, before choosing either scale threshold. |
| Exact coefficient in Theorem 1.3 | For each finite Euclidean admissible C, `ContinuousTransference.lean` cancels the same rᵈ from the two sides, proving it finite and positive for 0 < r < 1/2. The support enlargement appears as N + 1 in the input admissibility hypothesis. The limit produces the original periodic right side, retaining coefficient one. The measurable-weight step uses an almost-everywhere equal pointwise minorant, which controls every ray. The left side integrates over one unit of time and the Euclidean ray over all real times. |
| Test size and direction of comparison in Theorems 1.4 and 1.5 | Theorem 1.4 compares unpinned counts with Stein and pinned counts with MT, in both the box and exact-size models. In `WeightScales.lean` one block of length n and d−1 unit blocks produces a datum with **exactly n** frequencies in every positive dimension. The MT lower bound is n/4 and the Stein upper bound is n for all n ≥ 1. The proved inequality MT ≤ Stein supplies the two remaining bounds. The box lower constant can be taken to be (8d log 2)⁻ᵈ, positive in every asserted dimension. |

I found no discrepancy in these checks. The more detailed public-definition review describes the lower-integral convention on exceptional nonmeasurable ray restrictions and the use of frequency profiles for Euclidean initial data. Those conventions also apply to this review.

## Independent Lean elaboration

I transcribed the following selected consequences of the source in a fresh file and asked Lean to accept the named public proofs at those types. Copy the code below to `/tmp/rts-review-public-types.lean` and run `lake env lean /tmp/rts-review-public-types.lean` from the repository root.

```lean
import Solution
open RTS
open scoped ENNReal
example : ∃ c : ℝ, 0 < c ∧
    (∃ R : ℝ, ∀ N ≥ R, pinnedBoxRatio N ≤ boxRatio N ∧
      (Real.log N) ^ (c / Real.log (Real.log (Real.log N))) ≤ pinnedBoxRatio N) ∧
    (∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀, pinnedSizeRatio n ≤ sizeRatio n ∧
      (Real.log n) ^ (c / Real.log (Real.log (Real.log n))) ≤ pinnedSizeRatio n) :=
  combinatorial_growth
example (d : ℕ) (hd : d ≥ 1) (N : ℝ) (hN : N ≥ 1) :
    perStein d N ≤ eucStein d (N + 1) ∧ perMT d N ≤ eucMT d (N + 1) :=
  quantitative_transference d hd N hN
example (d : ℕ) (hd : d ≥ 1) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ n₀ : ℕ, n₀ ≥ 1 ∧ ∀ n ≥ n₀,
      ENNReal.ofReal (c * n) ≤ perSteinCard d n ∧
      ENNReal.ofReal (c * n) ≤ perMTCard d n ∧
      perSteinCard d n ≤ ENNReal.ofReal (C * n) ∧ perMTCard d n ≤ ENNReal.ofReal (C * n) :=
  (trigonometric_growth d hd).2
#check chebyshev_asymptotic_pnt (q := 4) (a := 3) (by decide) (by decide) (by decide)
#print axioms chebyshev_asymptotic_pnt
```

The command exited with status 0. Lean emitted no diagnostics for the three examples. The complete output for the two inspection commands was

```text
chebyshev_asymptotic_pnt (of_decide_eq_true (id (Eq.refl true))) (of_decide_eq_true (id (Eq.refl true)))
  (of_decide_eq_true
    (id
      (Eq.refl
        true))) : Asymptotics.IsEquivalent Filter.atTop
  (fun x => ∑ p ≤ ⌊x⌋₊ with Nat.Prime p, if p % 4 = 3 then Real.log ↑p else 0) fun x => x / ↑(Nat.totient 4)
'chebyshev_asymptotic_pnt' depends on axioms: [propext, Classical.choice, Quot.sound]
```
