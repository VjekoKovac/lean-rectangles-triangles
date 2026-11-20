module

public import RTS.WeightCollisions
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Section 5, lower bound for the numerator. A tuple of (r+1)-element subsets
and two choices of a marked element in each coordinate produce two terms of
the product with the same spacetime frequency. They determine the original
subsets and marks, so their number bounds the collision count from below. -/

@[expose] public section

namespace RTS.Dyadic

open Finset
variable {d : ℕ}

private def removeMark (J : Fin d → Finset ℕ) (j : Fin d → ℕ) : ProductIndex d :=
  (j, fun l => (J l).erase (j l))

private def decode (p : ProductIndex d) : Fin d → Finset ℕ :=
  fun l => insert (p.1 l) (p.2 l)

private theorem decode_removeMark {J : Fin d → Finset ℕ} {j : Fin d → ℕ}
    (hj : j ∈ Fintype.piFinset J) : decode (removeMark J j) = J := by
  funext l
  exact Finset.insert_erase (Fintype.mem_piFinset.mp hj l)

private theorem removeMark_mem {m r : Fin d → ℕ} {J : Fin d → Finset ℕ}
    (hJ : J ∈ family m (fun l => r l + 1)) {j : Fin d → ℕ}
    (hj : j ∈ Fintype.piFinset J) : removeMark J j ∈ testTerms m r := by
  apply Finset.mem_product.mpr
  constructor
  · exact Fintype.mem_piFinset.mpr fun l => (family_spec hJ l).1 (Fintype.mem_piFinset.mp hj l)
  · apply Fintype.mem_piFinset.mpr
    intro l
    apply mem_powersetCard.mpr
    constructor
    · exact (Finset.erase_subset _ _).trans (family_spec hJ l).1
    · simp [removeMark, Finset.card_erase_of_mem (Fintype.mem_piFinset.mp hj l), (family_spec hJ l).2]

private theorem marked_space (m : Fin d → ℕ) {J : Fin d → Finset ℕ} {j : Fin d → ℕ}
    (hj : j ∈ Fintype.piFinset J) : productSpace m (removeMark J j) = spaceFreq m J := by
  funext l
  exact Finset.add_sum_erase (J l) (fun i => (2 : ℤ) ^ (offset m l + i))
    (Fintype.mem_piFinset.mp hj l)

private theorem marked_time (m : Fin d → ℕ) {J : Fin d → Finset ℕ} {j : Fin d → ℕ}
    (hj : j ∈ Fintype.piFinset J) : productTime m (removeMark J j) = timeFreq m J := by
  unfold productTime timeFreq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  change ((2:ℤ) ^ (offset m l + j l))^2 +
    (∑ i ∈ (J l).erase (j l), (4:ℤ)^(offset m l+i)) = _
  rw [pow_right_comm (2:ℤ) _ 2, show (2:ℤ)^2 = 4 by decide]
  exact Finset.add_sum_erase (J l) (fun i => (4 : ℤ) ^ (offset m l + i)) (Fintype.mem_piFinset.mp hj l)

/-- The product of binomial coefficients with the squared representation multiplicity,
in the numerator of Lemma 5.1. -/
theorem collision_count_lower (m r : Fin d → ℕ) :
    (∏ l, (r l + 1)^2 * (m l).choose (r l + 1)) ≤ (collisions m r).card := by
  classical
  let s := (family m (fun l => r l + 1)).sigma fun J => Fintype.piFinset J ×ˢ Fintype.piFinset J
  let f (a : Σ _ : Fin d → Finset ℕ, (Fin d → ℕ) × (Fin d → ℕ)) :=
    (removeMark a.1 a.2.1, removeMark a.1 a.2.2)
  have hin : Set.MapsTo f (↑s) (↑(collisions m r)) := by
    intro a ha
    obtain ⟨hJ, hpair⟩ := mem_sigma.mp ha
    obtain ⟨hj,hk⟩ := mem_product.mp hpair
    exact mem_filter.mpr ⟨mem_product.mpr ⟨removeMark_mem hJ hj,removeMark_mem hJ hk⟩,
      (marked_space m hj).trans (marked_space m hk).symm,
      (marked_time m hj).trans (marked_time m hk).symm⟩
  have inj : Set.InjOn f (↑s) := by
    rintro ⟨J,j,k⟩ h1 ⟨K,j',k'⟩ h2 he
    have hj := (mem_product.mp (mem_sigma.mp h1).2).1
    have hj' := (mem_product.mp (mem_sigma.mp h2).2).1
    have eqJ := congrArg (fun z : ProductIndex d × ProductIndex d => decode z.1) he
    change decode (removeMark J j) = decode (removeMark K j') at eqJ
    rw [decode_removeMark hj, decode_removeMark hj'] at eqJ
    have eqj : j = j' := congrArg (fun z : ProductIndex d × ProductIndex d => z.1.1) he
    have eqk : k = k' := congrArg (fun z : ProductIndex d × ProductIndex d => z.2.1) he
    subst_vars
    rfl
  have hcard : s.card = ∏ l, (r l+1)^2 * (m l).choose (r l+1) := by
    rw [Finset.prod_mul_distrib]
    change ((family m _).sigma _).card = _
    rw [card_sigma]
    calc
      _ = ∑ _ ∈ family m (fun l => r l+1), ∏ l, (r l + 1)^2 := by
        apply sum_congr rfl
        intro J hJ
        rw [card_product, Fintype.card_piFinset, ← sq, ← Finset.prod_pow]
        exact Finset.prod_congr rfl fun l _ => congrArg (· ^ 2) (family_spec hJ l).2
      _ = _ := by simp [family_card, mul_comm]
  exact hcard ▸ card_le_card_of_injOn f hin inj

end RTS.Dyadic
