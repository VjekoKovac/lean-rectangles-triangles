module

public import RTS.CombinatorialProof
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators

/-! The integer lattice set of §2 and the monotonicity facts used for interpolation. -/

@[expose] public section

namespace RTS
open Finset

def intGrid (N : ℕ) : Finset Point :=
  Fintype.piFinset fun _ => Icc (-(N : ℤ)) (N : ℤ)

def circleLift (q N : ℕ) : Finset Point :=
  (intGrid N).filter fun k => Int.ModEq q (dot₂ k k) 1

theorem mem_circleLift {q N : ℕ} {k : Point} :
    k ∈ circleLift q N ↔ (∀ i, -(N:ℤ) ≤ k i ∧ k i ≤ N) ∧ Int.ModEq q (dot₂ k k) 1 := by
  simp [circleLift,intGrid]

theorem circleLift_mono (q : ℕ) : Monotone (circleLift q) := by
  intro m n h k hk
  obtain ⟨hbox, hmod⟩ := mem_circleLift.mp hk
  refine mem_circleLift.mpr ⟨fun i => ?_, hmod⟩
  have := hbox i
  omega

theorem circleLift_card_le (q N : ℕ) : (circleLift q N).card ≤ (2*N+1)^2 := by
  calc
    _ ≤ (intGrid N).card := card_filter_le (intGrid N) _
    _ = _ := by
      simp [intGrid, Int.card_Icc]
      omega

theorem circleLift_fitsBox (q N : ℕ) : FitsBox (N:ℝ) (circleLift q N) := by
  intro k hk i
  apply abs_le.mpr
  exact_mod_cast (mem_circleLift.mp hk).1 i

theorem circleLift_card_unbounded {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ∃ t, n ≤ (circleLift q t).card := by
  classical
  let pt (j : ℕ) : Point := ![(1:ℤ)+q*j,0]
  have hinj : Function.Injective pt := by
    intro i j h
    have hcoord := congrFun h 0
    have he : (q:ℤ) * i = q * j := by simpa [pt] using hcoord
    exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hq.ne') he
  use 1+q*n
  calc
    n = ((range n).image pt).card := by simp [card_image_of_injective _ hinj]
    _ ≤ _ := by
      apply card_le_card
      intro k hk
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
      have hjn : j ≤ n := (mem_range.mp hj).le
      have hqj : (q:ℤ)*j ≤ (q:ℤ)*n := by exact_mod_cast Nat.mul_le_mul_left q hjn
      have hpos : (0:ℤ) ≤ (q:ℤ)*j := by positivity
      apply mem_circleLift.mpr
      constructor
      · intro i
        fin_cases i <;> simp [pt] <;> omega
      · change Int.ModEq q (∑ i, pt j i * pt j i) 1
        simp [Fin.sum_univ_two,pt]
        apply Int.modEq_iff_dvd.mpr
        exact ⟨-2*(j:ℤ)-q*j^2, by ring⟩

private theorem sum_le_of_subset_mono {A B : Finset Point} (h : A ⊆ B)
    {f g : Point → ℕ} (hfg : ∀ i ∈ A, f i ≤ g i) :
    ∑ i ∈ A, f i ≤ ∑ i ∈ B, g i :=
  (Finset.sum_le_sum hfg).trans (Finset.sum_le_sum_of_subset_of_nonneg h (by intros; omega))

theorem rectangleCount_mono {A B : Finset Point} (h : A ⊆ B) :
    rectangleCount A ≤ rectangleCount B := by
  unfold rectangleCount
  exact sum_le_of_subset_mono h fun _ _ => sum_le_of_subset_mono h fun _ _ =>
    sum_le_of_subset_mono h fun _ _ => card_le_card (filter_subset_filter _ h)

theorem pinnedTriangleCount_mono {A B : Finset Point} (h : A ⊆ B) (k : Point) :
    pinnedTriangleCount A k ≤ pinnedTriangleCount B k := by
  unfold pinnedTriangleCount
  exact sum_le_of_subset_mono h fun _ _ => card_le_card (filter_subset_filter _ h)

theorem maxPinnedCount_mono {A B : Finset Point} (h : A ⊆ B) :
    maxPinnedCount A ≤ maxPinnedCount B := by
  unfold maxPinnedCount
  apply Finset.sup_le
  intro k hk
  exact (pinnedTriangleCount_mono h k).trans (Finset.le_sup (h hk))

theorem triangleCount_mono {A B : Finset Point} (h : A ⊆ B) :
    triangleCount A ≤ triangleCount B := by
  unfold triangleCount
  exact sum_le_of_subset_mono h fun k _ => pinnedTriangleCount_mono h k

theorem pinnedRatio_le_pinnedSizeRatio {A : Finset Point} (hA : A.Nonempty) :
    pinnedRatio A ≤ pinnedSizeRatio A.card := by
  unfold pinnedSizeRatio
  apply le_csSup
  · use (A.card : ℝ)^4
    rintro _ ⟨B, hB, rfl⟩
    have h : B.Nonempty := card_pos.mp (hB ▸ card_pos.mpr hA)
    exact (pinnedRatio_le_ratio h).trans (by simpa [hB] using ratio_le_card_fourth h)
  · exact ⟨A,rfl,rfl⟩

theorem pinnedRatio_le_pinnedBoxRatio {A : Finset Point} {N : ℝ} (hA : A.Nonempty)
    (hfit : FitsBox N A) : pinnedRatio A ≤ pinnedBoxRatio N := by
  unfold pinnedBoxRatio
  apply le_csSup
  · use ((intGrid ⌈N⌉₊).card : ℝ)^4
    rintro _ ⟨B,hB,hBox,rfl⟩
    apply (pinnedRatio_le_ratio hB).trans
    apply (ratio_le_card_fourth hB).trans
    gcongr
    intro k hk
    apply Fintype.mem_piFinset.mpr
    intro i
    apply mem_Icc.mpr
    exact_mod_cast abs_le.mp ((hBox k hk i).trans (Nat.le_ceil N))
  · exact ⟨A,hA,hfit,rfl⟩

end RTS
