module

public import RTS.LiftingTuples
public import RTS.LiftingThreshold

/-! # Upper bound for pinned side parameters in a residue class

Summing over all nonzero directions bounds the primitive sum from above.
For each direction the two scalar counts cost at most the square of the
one-dimensional progression count; retaining its constant term also covers
the two possible zero scalar parameters.
-/
@[expose] public noncomputable section
namespace RTS.Lifting
open Finset Real

theorem picks_card_upper {q : ℕ} (hq : 0 < q) (b c : ZMod q) {Y : ℝ} (hY : 0 ≤ Y) :
    ((picks q b c Y).card : ℝ) ≤ 8*(Y/q)^2+2 := by
  have H (a : ZMod q) : ((line q (a.val:ℤ) Y).card : ℝ) ≤ 2*Y/q+1 :=
    by linarith only [(abs_le.mp (line_card_error hq (a.val:ℤ) hY)).2]
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  calc
    _ ≤ (((line q (b.val:ℤ) Y) ×ˢ (line q (c.val:ℤ) Y)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card (erase_subset _ _)
    _ ≤ (2*Y/q+1)*(2*Y/q+1) := by
      rw [card_product,Nat.cast_mul]
      exact mul_le_mul (H b) (H c) (by positivity) (by positivity)
    _ ≤ _ := by
      rw [show 2*Y/q = 2*(Y/q) by ring]
      nlinarith only [sq_nonneg (2*(Y/q)-1)]

theorem sideFiber_pinned_upper {q : ℕ} (hq : 0 < q) (e : PinResidue q) {N : ℝ}
    (hN : (q:ℝ) ≤ N) :
    ((sideFiber q e (4*N) (4*N)).card : ℝ) ≤
      128*(N/q)^2 * (8*log (4*N)/(q:ℝ)^2 + 42) + 2*(9*N/q)^2 := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hn : 0 ≤ N := hq'.le.trans hN
  have ht : 1 ≤ 4*N := by linarith
  let S := directions q e.1 (4*N)
  have hs : S ⊆ nonzeroSquare q (representative e.1) (4*N) := Finset.filter_subset .. 
  have sum_bound : (∑ w ∈ S, 1/(radius w:ℝ)^2) ≤ 8*log (4*N)/(q:ℝ)^2+42 := by
    calc
      _ ≤ inverseSquareSum q (representative e.1) (4*N) :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
      _ ≤ _ := by linarith only [(abs_le.mp (inverseSquareSum_error hq (representative e.1) ht)).2]
  have card_bound : (S.card:ℝ) ≤ (9*N/q)^2 := by
    have hsq := (abs_le.mp (square_card_error hq (representative e.1) (show 0 ≤ 4*N by positivity))).2
    have h₁ : (S.card:ℝ) ≤ (square q (representative e.1) (4*N)).card := by
      exact_mod_cast Finset.card_le_card (hs.trans (Finset.erase_subset ..))
    have h₂ : 1 ≤ N/q := (one_le_div hq').2 hN
    rw [show 2*(4*N)/q = 8*(N/q) by ring] at hsq
    calc
      _ ≤ (8*(N/q)+1)^2 := by nlinarith only [h₁,hsq]
      _ ≤ _ := by
        apply pow_le_pow_left₀ (by positivity)
        rw [show 9*N/q = 9*(N/q) by ring]
        linarith only [h₂]
  have one (w : Point) :
      ((picks q e.2.1 e.2.2 (4*N/(radius w:ℝ))).card:ℝ) ≤
        (128*(N/q)^2) * (1/(radius w:ℝ)^2) + 2 := by
    convert picks_card_upper hq e.2.1 e.2.2 (Y := 4*N/(radius w:ℝ)) (by positivity) using 1
    ring
  have count : (sideFiber q e (4*N) (4*N)).card ≤
      ∑ w ∈ S, (picks q e.2.1 e.2.2 (4*N/(radius w:ℝ))).card := by
    unfold sideFiber
    exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun w _ => Finset.card_image_le)
  calc
    _ ≤ ∑ w ∈ S, ((picks q e.2.1 e.2.2 (4*N/(radius w:ℝ))).card:ℝ) := by exact_mod_cast count
    _ ≤ ∑ w ∈ S, ((128*(N/q)^2) * (1/(radius w:ℝ)^2) + 2) :=
      sum_le_sum (fun w _ => one w)
    _ = (128*(N/q)^2) * (∑ w ∈ S, 1/(radius w:ℝ)^2) + 2*S.card := by
      simp [sum_add_distrib,← Finset.mul_sum,mul_comm (2:ℝ)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left sum_bound (by positivity))
      (mul_le_mul_of_nonneg_left card_bound (by norm_num))

theorem pinTupleSet_upper {q : ℕ} (hq : 0 < q) (F : Finset (PinResidue q)) {N : ℝ}
    (hN : (q:ℝ) ≤ N) :
    ((pinTupleSet q F N).card:ℝ) ≤ (F.card:ℝ) *
      (128*(N/q)^2 * (8*log (4*N)/(q:ℝ)^2 + 42) + 2*(9*N/q)^2) := by
  calc
    _ ≤ ((∑ e ∈ F, (sideFiber q e (4*N) (4*N)).card : ℕ):ℝ) := by
      unfold pinTupleSet
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ _ := by
      rw [Nat.cast_sum, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun e _ => sideFiber_pinned_upper hq e hN

/-- Uniform upper bound at the single exponential threshold used by the lift. -/
theorem pinTupleSet_upper_threshold {q : ℕ} (hq : 0 < q) (F : Finset (PinResidue q)) {N : ℝ}
    (hN : exp (1000*(q:ℝ)^2) ≤ N) :
    ((pinTupleSet q F N).card:ℝ) ≤ 10000*F.card*N^2*log N/(q:ℝ)^4 := by
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hqN : (q:ℝ) ≤ N := by
    have he := Real.add_one_le_exp (1000*(q:ℝ)^2)
    nlinarith [sq_nonneg ((q:ℝ)-1)]
  calc
    _ ≤ _ := pinTupleSet_upper hq F hqN
    _ ≤ (F.card:ℝ)*(10000*N^2*log N/(q:ℝ)^4) :=
      mul_le_mul_of_nonneg_left (lifting_upper_threshold hq hN) (by positivity)
    _ = _ := by ring

end RTS.Lifting
