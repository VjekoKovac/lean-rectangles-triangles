module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-! # Arithmetic of the lacunary test weight

The argument for the X-ray identity in §5 of Bennett–Kovač–Nakamura–Oliveira
uses one odd summand at the least power of two. The exponents are computed
without any restrictions on the block lengths other than those in the paper.
-/
@[expose] public section

namespace RTS.Dyadic

open Finset

/-- Frequency in time after restriction to the geodesic of dyadic index `q`. -/
def timeTerm (M q j : ℕ) : ℤ :=
  2 ^ (2 * M) * (2 ^ (2 * j) - 2 ^ (j + q + 1))

/-- Exponent of two in a nonzero time term. -/
def order (M q j : ℕ) : ℕ := 2 * M + min (2*j) (j+q+1)

private theorem pow_sub_pow_odd {a b : ℕ} (h : a < b) :
    ∃ z : ℤ, ¬ 2 ∣ z ∧ (2:ℤ)^a - 2^b = 2^a * z := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show a + 1 ≤ b by omega)
  refine ⟨1 - 2 * 2^k, ?_, ?_⟩
  · omega
  · rw [pow_add, pow_succ]
    ring

theorem timeTerm_factor {M q j : ℕ} (h : j ≠ q+1) :
    ∃ z : ℤ, ¬ 2 ∣ z ∧ timeTerm M q j = 2 ^ order M q j * z := by
  rcases lt_or_gt_of_ne (show 2*j ≠ j+q+1 by omega) with hlt | hgt
  · obtain ⟨z,hz,he⟩ := pow_sub_pow_odd hlt
    exact ⟨z,hz,by unfold timeTerm order; rw [min_eq_left hlt.le, he, pow_add]; ring⟩
  · obtain ⟨z,hz,he⟩ := pow_sub_pow_odd hgt
    refine ⟨-z, by simpa using hz, ?_⟩
    simp only [timeTerm, order, min_eq_right hgt.le, pow_add]
    linear_combination -(2:ℤ)^(2*M) * he

/-- A sum of odd multiples of distinct powers of two cannot vanish. -/
theorem sum_ne_zero_of_distinct_orders {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (v : ι → ℕ) (f : ι → ℤ) (hv : Set.InjOn v (↑s : Set ι))
    (hf : ∀ i ∈ s, ∃ z : ℤ, ¬ 2 ∣ z ∧ f i = 2 ^ v i * z) :
    ∑ i ∈ s, f i ≠ 0 := by
  classical
  intro hzero
  obtain ⟨i, hi, hmin⟩ := s.exists_min_image v hs
  obtain ⟨z,hz,he⟩ := hf i hi
  have hd : (2:ℤ) ^ (v i+1) ∣ ∑ j ∈ s.erase i, f j := by
    apply Finset.dvd_sum
    intro j hj
    obtain ⟨hne,hj'⟩ := Finset.mem_erase.mp hj
    have hlt : v i < v j := lt_of_le_of_ne (hmin j hj') (fun h => hne (hv hj' hi h.symm))
    obtain ⟨w, _, hw⟩ := hf j hj'
    rw [hw]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ hlt) _
  have hneg : ∑ j ∈ s.erase i, f j = -f i := by
    have := s.sum_erase_add f hi
    omega
  rw [hneg, dvd_neg, he, pow_succ] at hd
  exact hz ((mul_dvd_mul_iff_left (by positivity : (2:ℤ)^v i ≠ 0)).mp hd)

/-- The index intervals of different coordinate blocks are disjoint. -/
def offset {d : ℕ} (m : Fin d → ℕ) (l : Fin d) : ℕ :=
  ∑ h ∈ Finset.univ.filter (· < l), m h

theorem offset_add_le {d : ℕ} {m : Fin d → ℕ} {a b : Fin d} (h : a < b) :
    offset m a + m a ≤ offset m b := by
  classical
  let s := Finset.univ.filter (· < a)
  have hnot : a ∉ s := by simp [s]
  have hs : insert a s ⊆ Finset.univ.filter (· < b) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simpa using h
    · have : j < a := by simpa [s] using hj
      simpa using this.trans h
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := m) hs (by intros; omega)
  simpa [offset, s, Finset.sum_insert hnot, Nat.add_comm] using this

/-- The source's two ranges of valuations give a single strictly increasing
sequence inside each block. Distinct blocks also have distinct valuations. -/
theorem orders_injective {d : ℕ} (m q : Fin d → ℕ)
    {a b : Fin d} {i j : ℕ} (hi : 1 ≤ i) (him : i ≤ m a) (hj : 1 ≤ j) (hjm : j ≤ m b)
    (he : order (offset m a) (q a) i = order (offset m b) (q b) j) :
    a = b ∧ i = j := by
  have hab : a = b := by
    rcases lt_trichotomy a b with h | h | h
    · have ho := offset_add_le (m := m) h
      simp only [order] at he
      omega
    · exact h
    · have ho := offset_add_le (m := m) h
      simp only [order] at he
      omega
  subst b
  exact ⟨rfl, by unfold order at he; omega⟩

/-- A zero signed sum on the nonexceptional block indices forces every
coefficient to vanish. The coefficients are differences of two indicators. -/
theorem signed_dyadic_rigidity {d : ℕ} (m q : Fin d → ℕ) (s : Finset (Fin d × ℕ))
    (hs : ∀ p ∈ s, 1 ≤ p.2 ∧ p.2 ≤ m p.1 ∧ p.2 ≠ q p.1 + 1)
    (c : Fin d × ℕ → ℤ) (hc : ∀ p ∈ s, c p = -1 ∨ c p = 0 ∨ c p = 1)
    (hzero : ∑ p ∈ s, c p * timeTerm (offset m p.1) (q p.1) p.2 = 0) :
    ∀ p ∈ s, c p = 0 := by
  classical
  let f := fun p : Fin d × ℕ => c p * timeTerm (offset m p.1) (q p.1) p.2
  let t := s.filter (fun p => c p ≠ 0)
  intro p hp
  by_contra hp'
  have hne : t.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp,hp'⟩⟩
  apply sum_ne_zero_of_distinct_orders hne
    (fun x => order (offset m x.1) (q x.1) x.2) f
  · intro x hx y hy he
    obtain ⟨hx1,hx2,_⟩ := hs x (Finset.mem_filter.mp hx).1
    obtain ⟨hy1,hy2,_⟩ := hs y (Finset.mem_filter.mp hy).1
    exact Prod.ext (orders_injective m q hx1 hx2 hy1 hy2 he).1
      (orders_injective m q hx1 hx2 hy1 hy2 he).2
  · intro x hx
    obtain ⟨hx,hcn⟩ := Finset.mem_filter.mp hx
    obtain ⟨z,hz,he⟩ := timeTerm_factor (M := offset m x.1) (hs x hx).2.2
    rcases hc x hx with h | h | h
    · exact ⟨-z, by simpa using hz, by simp [f, h, he]⟩
    · contradiction
    · exact ⟨z, hz, by simp [f, h, he]⟩
  · calc ∑ x ∈ t, f x = ∑ x ∈ s, f x := by
          exact Finset.sum_subset (Finset.filter_subset ..) (by
            intro x hx hxt
            have : c x = 0 := by simpa [t, hx] using hxt
            simp [f, this])
         _ = 0 := hzero

/-- The floor-half choice in §5 gives the explicit single-coordinate bound
`m / 4`; this holds even for `m = 1`. -/
theorem quarter_le_dyadic_ratio (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / 4 ≤ ((m / 2 + 1 : ℕ) : ℝ) * ((m - m/2 : ℕ) : ℝ) / m := by
  have h₁ : m ≤ 2 * (m/2+1) := by omega
  have h₂ : m ≤ 2 * (m-m/2) := by omega
  have h := Nat.mul_le_mul h₁ h₂
  have hR : (m:ℝ) * m ≤ (2 * ((m / 2 + 1 : ℕ) : ℝ)) * (2 * ((m - m / 2 : ℕ) : ℝ)) := by
    exact_mod_cast h
  apply (le_div_iff₀ (by exact_mod_cast hm)).mpr
  linarith

/-- Elimination of adjacent binomial coefficients in the ratio of test integrals. -/
theorem dyadic_binomial_ratio (m r : ℕ) (hm : 0 < m) (hr : r ≤ m) :
    (r + 1 : ℝ)^2 * (m.choose (r+1) : ℝ) / ((m:ℝ) * m.choose r) =
    (r+1:ℝ) * ((m-r : ℕ):ℝ) / m := by
  have h := Nat.choose_succ_right_eq m r
  have hc : (m.choose (r+1):ℝ) * (r+1:ℝ) = (m.choose r : ℝ) * ((m-r : ℕ):ℝ) := by
    exact_mod_cast h
  have hm' : (m:ℝ) ≠ 0 := by positivity
  have hchoose : (m.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  field_simp
  nlinarith [congrArg (fun z : ℝ => (r+1) * z) hc]

end RTS.Dyadic
