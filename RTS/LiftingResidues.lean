module

public import RTS.LiftingCounts
public import Mathlib.Data.ZMod.Basic

/-! The last assertion of Lemma 2.4 for arbitrary sets of residue classes. -/
@[expose] public noncomputable section

namespace RTS.Lifting
open Finset
open scoped BigOperators

abbrev Residue (q : ℕ) := Fin 2 → ZMod q
abbrev reduce (q : ℕ) (w : Point) : Residue q := fun i => w i

def pointsInResidue (q : ℕ) (a : Residue q) (T : ℝ) := square q (fun i => (a i).val) T

theorem mem_pointsInResidue {q : ℕ} (hq : 0 < q) {a : Residue q} {w : Point} {T : ℝ} :
    w ∈ pointsInResidue q a T ↔ (∀ i, |(w i : ℝ)| ≤ T) ∧ reduce q w = a := by
  haveI : NeZero q := ⟨hq.ne'⟩
  simp only [pointsInResidue, mem_square hq, ← ZMod.intCast_eq_intCast_iff_dvd_sub,
    Int.cast_natCast, ZMod.natCast_zmod_val, forall_and, reduce, funext_iff]
  exact and_congr_right fun _ => forall_congr' fun _ => eq_comm

def liftedSet (q : ℕ) (B : Finset (Residue q)) (T : ℝ) := B.biUnion (pointsInResidue q · T)

theorem mem_liftedSet {q : ℕ} (hq : 0 < q) {B : Finset (Residue q)} {w : Point} {T : ℝ} :
    w ∈ liftedSet q B T ↔ (∀ i, |(w i : ℝ)| ≤ T) ∧ reduce q w ∈ B := by
  simp only [liftedSet, mem_biUnion, mem_pointsInResidue hq]
  aesop

/-- The source's bound (ANuniform), with the explicit absolute error constant 5. -/
theorem liftedSet_card_error {q : ℕ} (hq : 0 < q) (B : Finset (Residue q)) {T : ℝ}
    (hT : (q : ℝ) ≤ T) :
    |((liftedSet q B T).card : ℝ) - 4*(B.card : ℝ)*T^2/(q:ℝ)^2| ≤ 5*B.card*T/q := by
  have hp : 0 < (q:ℝ) := by exact_mod_cast hq
  have ht : 0 ≤ T := hp.le.trans hT
  have hc : (liftedSet q B T).card = ∑ a ∈ B, (pointsInResidue q a T).card := by
    apply Finset.card_biUnion
    intro a ha b hb hab
    rw [Function.onFun, disjoint_left]
    intro w hwa hwb
    exact hab (((mem_pointsInResidue hq).mp hwa).2.symm.trans ((mem_pointsInResidue hq).mp hwb).2)
  rw [hc, Nat.cast_sum]
  have hm : 4*(B.card : ℝ)*T^2/(q:ℝ)^2 = ∑ _a ∈ B, (2*T/q)^2 := by simp; ring
  rw [hm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ B, |((pointsInResidue q a T).card : ℝ) - (2*T/q)^2| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _a ∈ B, (2*(2*T/q)+1) :=
      sum_le_sum fun a _ => square_card_error hq _ ht
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      have hv : 1 ≤ T/q := (one_le_div hp).2 hT
      have := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α := ℝ) B.card)
      linarith only [show 5*(B.card:ℝ)*T/q - (B.card:ℝ)*(2*(2*T/q)+1) =
        (B.card:ℝ)*(T/q)-(B.card:ℝ)*1 by ring, this]

end RTS.Lifting
