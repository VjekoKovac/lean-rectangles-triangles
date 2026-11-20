module

public import RTS.Combinatorics
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

namespace RTS

open scoped BigOperators

theorem isTriangle_diagonal (a k : Point) : IsTriangle a a k := by
  simp [IsTriangle, dot₂]

theorem card_le_pinnedTriangleCount (A : Finset Point) (k : Point) :
    A.card ≤ pinnedTriangleCount A k := by
  unfold pinnedTriangleCount
  calc
    A.card = ∑ _ ∈ A, 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, isTriangle_diagonal a k⟩⟩

theorem card_sq_le_triangleCount (A : Finset Point) : A.card ^ 2 ≤ triangleCount A := by
  calc
    A.card ^ 2 = ∑ _ ∈ A, A.card := by simp [sq]
    _ ≤ _ := Finset.sum_le_sum fun k _ => card_le_pinnedTriangleCount A k

theorem triangleCount_le_card_mul_max (A : Finset Point) :
    triangleCount A ≤ A.card * maxPinnedCount A := by
  calc
    _ ≤ ∑ _ ∈ A, maxPinnedCount A := Finset.sum_le_sum fun k hk => Finset.le_sup hk
    _ = _ := by simp

theorem pinnedRatio_le_ratio {A : Finset Point} (h : A.Nonempty) : pinnedRatio A ≤ ratio A := by
  have ht : 0 < triangleCount A :=
    lt_of_lt_of_le (pow_pos (Finset.card_pos.mpr h) 2) (card_sq_le_triangleCount A)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast ht)
    (by exact_mod_cast triangleCount_le_card_mul_max A)

theorem rectangleCount_le_card_fourth (A : Finset Point) : rectangleCount A ≤ A.card ^ 4 := by
  unfold rectangleCount
  calc
    _ ≤ ∑ _ ∈ A, ∑ _ ∈ A, ∑ _ ∈ A, A.card :=
      Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
        Finset.sum_le_sum fun _ _ => Finset.card_filter_le .. 
    _ = _ := by simp; ring

theorem ratio_le_card_fourth {A : Finset Point} (h : A.Nonempty) : ratio A ≤ (A.card : ℝ)^4 := by
  have ht : 1 ≤ triangleCount A :=
    lt_of_lt_of_le (pow_pos (Finset.card_pos.mpr h) 2) (card_sq_le_triangleCount A)
  exact le_trans (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast ht))
    (by exact_mod_cast rectangleCount_le_card_fourth A)

private noncomputable def grid (N : ℝ) : Finset Point :=
  Fintype.piFinset fun _ => Finset.Icc (-⌈N⌉) ⌈N⌉

private theorem subset_grid {N : ℝ} {A : Finset Point} (h : FitsBox N A) : A ⊆ grid N := by
  intro k hk
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have hh := abs_le.mp (le_trans (h k hk i) (Int.le_ceil N))
  exact_mod_cast hh

theorem pinnedBoxRatio_le_boxRatio {N : ℝ} (hN : 0 ≤ N) :
    pinnedBoxRatio N ≤ boxRatio N := by
  have h₀ : FitsBox N {0} := by simpa [FitsBox] using hN
  unfold pinnedBoxRatio boxRatio
  apply csSup_le
  · exact ⟨_, {0}, Finset.singleton_nonempty _, h₀, rfl⟩
  rintro _ ⟨A, hA, hbox, rfl⟩
  apply le_trans (pinnedRatio_le_ratio hA)
  apply le_csSup
  rotate_left
  · exact ⟨A, hA, hbox, rfl⟩
  use ((grid N).card : ℝ)^4
  rintro _ ⟨B, hB, hfit, rfl⟩
  apply le_trans (ratio_le_card_fourth hB)
  gcongr
  exact subset_grid hfit

theorem pinnedSizeRatio_le_sizeRatio {n : ℕ} (hn : 0 < n) :
    pinnedSizeRatio n ≤ sizeRatio n := by
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq Point n
  unfold pinnedSizeRatio sizeRatio
  apply csSup_le
  · exact ⟨_, A, hA, rfl⟩
  rintro _ ⟨B, hB, rfl⟩
  apply le_trans (pinnedRatio_le_ratio (Finset.card_pos.mp (by omega)))
  apply le_csSup
  rotate_left
  · exact ⟨B, hB, rfl⟩
  use (n : ℝ)^4
  rintro _ ⟨C, hC, rfl⟩
  rw [← hC]
  exact ratio_le_card_fourth (Finset.card_pos.mp (by omega))

end RTS
