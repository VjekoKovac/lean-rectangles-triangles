module

public import RTS.LiftingTuples

@[expose] public noncomputable section

namespace RTS.Lifting
open Finset

theorem sideFiber_card (q : ℕ) (e : PinResidue q) (T U : ℝ) :
    (sideFiber q e T U).card = ∑ w ∈ directions q e.1 T,
      (picks q e.2.1 e.2.2 (U/(radius w:ℝ))).card := by
  classical
  unfold sideFiber
  rw [card_biUnion]
  · exact sum_congr rfl fun w _ => card_image_of_injective _ (Prod.mk_right_injective w)
  · intro a _ b _ hab
    rw [Function.onFun, disjoint_left]
    rintro p ha hb
    obtain ⟨x,_,rfl⟩ := mem_image.mp ha
    obtain ⟨y,_,h⟩ := mem_image.mp hb
    exact hab (congrArg Prod.fst h).symm

theorem rectTupleSet_card {q : ℕ} (hq : 0 < q) (E : Finset (RectResidue q)) (N : ℝ) :
    (rectTupleSet q E N).card = ∑ e ∈ E, (rectFiber q e N).card := by
  classical
  apply card_biUnion
  intro a _ b _ hab
  rw [Function.onFun, disjoint_left]
  intro p ha hb
  have id (e : RectResidue q) (he : p ∈ rectFiber q e N) : rectResidue q p = e :=
    Prod.ext ((mem_pointsInResidue hq).mp (mem_product.mp he).1).2
      (((mem_sideFiber hq ..).mp (mem_product.mp he).2).1)
  exact hab ((id _ ha).symm.trans (id _ hb))

theorem picks_lower {q : ℕ} (hq : 0 < q) (b c : ZMod q) {Y : ℝ} (hY : 2 ≤ Y/q) :
    (Y/q)^2/2 ≤ ((picks q b c Y).card : ℝ) := by
  have hp : (0:ℝ) < q := by exact_mod_cast hq
  have hY₀ : 0 ≤ Y := by
    have hh := (le_div_iff₀ hp).mp hY
    linarith
  let B := line q (b.val:ℤ) Y
  let D := line q (c.val:ℤ) Y
  have hb : Y/q ≤ (B.card : ℝ) := by
    have hh := (abs_le.mp (line_card_error hq (b.val:ℤ) hY₀)).1
    change -(1:ℝ) ≤ B.card-2*Y/q at hh
    rw [show 2*Y/q=2*(Y/q) by ring] at hh
    linarith
  have hc : Y/q ≤ (D.card : ℝ) := by
    have hh := (abs_le.mp (line_card_error hq (c.val:ℤ) hY₀)).1
    change -(1:ℝ) ≤ D.card-2*Y/q at hh
    rw [show 2*Y/q=2*(Y/q) by ring] at hh
    linarith
  have hmul := mul_le_mul hb hc (by linarith : 0 ≤ Y/q) (Nat.cast_nonneg B.card)
  have hcou : B.card*D.card ≤ (picks q b c Y).card+1 := by
    rw [← card_product]
    change (B ×ˢ D).card ≤ ((B ×ˢ D).erase (0,0)).card + 1
    by_cases ht : (0,0) ∈ B ×ˢ D
    · exact (card_erase_add_one ht).ge
    · simp [erase_eq_of_notMem ht]
  have hreal : (B.card:ℝ)*(D.card:ℝ) ≤ (picks q b c Y).card+1 := by exact_mod_cast hcou
  nlinarith [sq_nonneg (Y/q-2)]

end RTS.Lifting
