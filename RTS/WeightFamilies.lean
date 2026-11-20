module

public import RTS.Dyadic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Nat

/-! # Subset frequencies and injectivity along dyadic test lines -/

@[expose] public section
namespace RTS.Dyadic
open Finset
variable {d : ℕ}

def indexBox (m : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun l => Icc 1 (m l))

def family (m r : Fin d → ℕ) : Finset (Fin d → Finset ℕ) :=
  Fintype.piFinset (fun l => (Icc 1 (m l)).powersetCard (r l))

theorem family_spec {m r : Fin d → ℕ} {J : Fin d → Finset ℕ} (h : J ∈ family m r) (l : Fin d) :
    J l ⊆ Icc 1 (m l) ∧ (J l).card = r l :=
  mem_powersetCard.mp (Fintype.mem_piFinset.mp h l)

theorem indexBox_card (m : Fin d → ℕ) : (indexBox m).card = ∏ l, m l := by
  simp [indexBox, Nat.card_Icc]

theorem family_card (m r : Fin d → ℕ) : (family m r).card = ∏ l, (m l).choose (r l) := by
  simp [family, card_powersetCard, Nat.card_Icc]

def frequency (m j : Fin d → ℕ) : Fin d → ℤ := fun l => 2^(offset m l + j l)
def spaceFreq (m : Fin d → ℕ) (J : Fin d → Finset ℕ) : Fin d → ℤ :=
  fun l => ∑ j ∈ J l, 2 ^ (offset m l + j)
def timeFreq (m : Fin d → ℕ) (J : Fin d → Finset ℕ) : ℤ :=
  ∑ l, ∑ j ∈ J l, 4 ^ (offset m l + j)
def lineFreq (m q : Fin d → ℕ) (J : Fin d → Finset ℕ) : ℤ :=
  timeFreq m J - ∑ l, 2 * frequency m q l * spaceFreq m J l

theorem frequency_injective (m : Fin d → ℕ) : Function.Injective (frequency m) := by
  intro j k h
  funext l
  have H : (2:ℤ)^(offset m l+j l) = 2^(offset m l+k l) := congrFun h l
  have := (pow_right_injective₀ (by norm_num : (0:ℤ) < 2) (by norm_num)) H
  omega

theorem lineFreq_sum (m q : Fin d → ℕ) (J : Fin d → Finset ℕ) :
    lineFreq m q J = ∑ l, ∑ j ∈ J l, timeTerm (offset m l) (q l) j := by
  unfold lineFreq timeFreq spaceFreq frequency
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (4:ℤ) = 2^2 by norm_num, ← pow_mul]
  simp only [timeTerm, pow_add, Nat.mul_add, pow_mul]
  ring_nf
  simp only [mul_comm (offset m l) 2, pow_mul]
  norm_num
  ring

private theorem eq_of_off_exception {A B : Finset ℕ} {e : ℕ} (hab : A.card = B.card)
    (h : ∀ j, j ≠ e → (j ∈ A ↔ j ∈ B)) : A = B := by
  have he : A.erase e = B.erase e := by
    ext j
    by_cases hj : j = e
    · simp [hj]
    · simp [hj, h j hj]
  by_cases ha : e ∈ A
  · have hb : e ∈ B := by
      by_contra hb
      have hcard := congrArg Finset.card he
      rw [card_erase_of_mem ha, erase_eq_of_notMem hb, ← hab] at hcard
      have := Finset.card_pos.mpr ⟨e,ha⟩
      omega
    simpa [ha,hb] using congrArg (insert e) he
  · have hb : e ∉ B := by
      intro hb
      have hcard := congrArg Finset.card he
      rw [card_erase_of_mem hb, erase_eq_of_notMem ha, hab] at hcard
      have := Finset.card_pos.mpr ⟨e,hb⟩
      omega
    simpa [ha,hb] using he

/-- At every tested velocity, different fixed-cardinality tuples of subsets
have different time frequencies on the line. This includes the exceptional
index of zero individual time frequency. -/
theorem lineFreq_injOn (m q r : Fin d → ℕ) :
    Set.InjOn (lineFreq m q) (↑(family m r) : Set (Fin d → Finset ℕ)) := by
  classical
  intro J hJ K hK he
  let U : Finset ℕ := Finset.univ.biUnion (fun l => J l ∪ K l)
  let all : Finset (Fin d × ℕ) := Finset.univ ×ˢ U
  let good := all.filter fun p => 1 ≤ p.2 ∧ p.2 ≤ m p.1 ∧ p.2 ≠ q p.1 + 1
  let c (p : Fin d × ℕ) : ℤ := (if p.2 ∈ J p.1 then 1 else 0) - (if p.2 ∈ K p.1 then 1 else 0)
  let f (p : Fin d × ℕ) := timeTerm (offset m p.1) (q p.1) p.2
  have hJU (l : Fin d) : J l ⊆ U := fun j hj => mem_biUnion.mpr ⟨l,mem_univ _,mem_union_left _ hj⟩
  have hKU (l : Fin d) : K l ⊆ U := fun j hj => mem_biUnion.mpr ⟨l,mem_univ _,mem_union_right _ hj⟩
  have sum_subset_ind (V : Finset ℕ) (hV : V ⊆ U) (g : ℕ → ℤ) :
      ∑ j ∈ U, (if j ∈ V then (1:ℤ) else 0) * g j = ∑ j ∈ V, g j := by
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
    congr 1
    ext j
    simp only [mem_filter]
    exact ⟨And.right, fun h => ⟨hV h,h⟩⟩
  have hsum : ∑ p ∈ all, c p * f p = 0 := by
    rw [lineFreq_sum, lineFreq_sum] at he
    unfold all
    rw [Finset.sum_product]
    simp only [c, sub_mul, Finset.sum_sub_distrib, f]
    simp_rw [sum_subset_ind _ (hJU _) _, sum_subset_ind _ (hKU _) _]
    exact sub_eq_zero.mpr he
  have hout (p : Fin d × ℕ) (hp : p ∈ all) (hg : p ∉ good) : c p * f p = 0 := by
    by_cases h : p.2 = q p.1 + 1
    · have e : 2*p.2 = p.2 + q p.1 + 1 := by omega
      simp [f, timeTerm, e]
    · have hu : p.2 ∉ Icc 1 (m p.1) := fun hx => hg <|
        mem_filter.mpr ⟨hp,(mem_Icc.mp hx).1,(mem_Icc.mp hx).2,h⟩
      have hj : p.2 ∉ J p.1 := fun hmem => hu ((family_spec hJ _).1 hmem)
      have hk : p.2 ∉ K p.1 := fun hmem => hu ((family_spec hK _).1 hmem)
      simp [c,hj,hk]
  have hzero := signed_dyadic_rigidity m q good (fun p hp => (mem_filter.mp hp).2) c
    (fun p _ => by dsimp [c]; split <;> split <;> decide)
    (show ∑ p ∈ good, c p * f p = 0 from
      (Finset.sum_subset (filter_subset ..) hout).trans hsum)
  funext l
  apply eq_of_off_exception (e := q l + 1) ((family_spec hJ l).2.trans (family_spec hK l).2.symm)
  intro j hj
  by_cases h : j ∈ J l ∨ j ∈ K l
  · have hu : j ∈ U := h.elim (fun h => hJU l h) (fun h => hKU l h)
    have hb : j ∈ Icc 1 (m l) := h.elim (fun h => (family_spec hJ l).1 h) (fun h => (family_spec hK l).1 h)
    have H := hzero (l,j) (mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, hu⟩,
      (mem_Icc.mp hb).1, (mem_Icc.mp hb).2, hj⟩)
    by_cases h₁ : j ∈ J l <;> by_cases h₂ : j ∈ K l <;> simp_all [c]
  · tauto

end RTS.Dyadic
