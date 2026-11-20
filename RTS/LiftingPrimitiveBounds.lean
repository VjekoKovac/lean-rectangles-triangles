module

public import RTS.LiftingTuples
public import RTS.LiftingSieveBounds
public import RTS.PrimitiveSieve

@[expose] public noncomputable section
namespace RTS.Lifting
open Finset

theorem directions_lower {q : ℕ} (hq : 0 < q) (a : Residue q)
    (ha : (Nat.gcd (a 0).val (a 1).val).Coprime q) {T : ℝ} (hT : 1 ≤ T) :
    2*Real.log T/(q:ℝ)^2 - 74 ≤ ∑ w ∈ directions q a T, 1/(radius w:ℝ)^2 := by
  have hc : (content (representative a)).Coprime q := by simpa [representative,content] using ha
  change _ ≤ primitiveInverseSquareSum q (representative a) T
  rw [primitive_inverseSquare_expansion hq _ hc]
  exact moebius_sum_lower hq _ hT

theorem directions_upper {q : ℕ} (hq : 0 < q) (a : Residue q) {T : ℝ} (hT : 1 ≤ T) :
    (∑ w ∈ directions q a T, 1/(radius w:ℝ)^2) ≤ 8*Real.log T/(q:ℝ)^2 + 42 := by
  have hh := (abs_le.mp (inverseSquareSum_error hq (representative a) hT)).2
  have hsub : (∑ w ∈ directions q a T, 1/(radius w:ℝ)^2) ≤
      inverseSquareSum q (representative a) T :=
    sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; positivity)
  linarith

end RTS.Lifting
