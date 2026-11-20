module

public import PrimeNumberTheoremAnd.Consequences

/-! Prime number theorem input to Section 2, following the source's choice of primes
congruent to three modulo four. The weighted prime number theorem is the previously
formalized theorem `chebyshev_asymptotic_pnt` of PrimeNumberTheoremAnd. -/

@[expose] public section
noncomputable section

namespace RTS

open Finset Filter Real
open scoped Topology

private def primesThree (n : ℕ) := (Iic n).filter fun p => p.Prime ∧ p % 4 = 3

private theorem many_primes_three :
    ∀ᶠ m : ℕ in atTop, m ≤ (primesThree (m^2)).card := by
  have hP := chebyshev_asymptotic_pnt (q := 4) (a := 3) (by decide) (by decide) (by decide)
  have htot : Nat.totient 4 = 2 := by decide
  rw [htot] at hP
  have hlim := (Asymptotics.isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    positivity)).mp hP
  have hhalf := hlim.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ) < 1))
  have hpow : Tendsto (fun m : ℕ => (m : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hlog := tendsto_natCast_atTop_atTop.eventually
    (Real.isLittleO_log_id_atTop.bound (by norm_num : 0 < (1/8:ℝ)))
  filter_upwards [hpow.eventually hhalf, hlog, eventually_ge_atTop (2:ℕ)] with m hm hlog hm2
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlogpos : 0 < log (m:ℝ) := log_pos (by exact_mod_cast (show 1 < m by omega))
  change ‖log (m:ℝ)‖ ≤ _ * ‖(m:ℝ)‖ at hlog
  rw [Real.norm_eq_abs, abs_of_pos hlogpos, Real.norm_eq_abs, abs_of_pos hmpos] at hlog
  change 1/2 < (∑ p ∈ (Iic ⌊(m:ℝ)^2⌋₊).filter Nat.Prime,
    if p%4 = 3 then log p else 0) / ((m:ℝ)^2 / (2:ℕ)) at hm
  have hfl : ⌊(m:ℝ)^2⌋₊ = m^2 := by rw [← Nat.cast_pow, Nat.floor_natCast]
  rw [hfl, ← Finset.sum_filter, Finset.filter_filter] at hm
  have hlo := (lt_div_iff₀ (by positivity)).mp hm
  change _ < ∑ p ∈ primesThree (m^2), log p at hlo
  have hup : (∑ p ∈ primesThree (m^2), log p) ≤
      ((primesThree (m^2)).card : ℝ) * (2 * log (m:ℝ)) := by
    calc
      _ ≤ ∑ _ ∈ primesThree (m^2), 2 * log (m:ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hp',hprime,_⟩ := Finset.mem_filter.mp hp
        rw [← show log ((m:ℝ)^2) = 2 * log (m:ℝ) by rw [Real.log_pow]; norm_num]
        exact Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast Finset.mem_Iic.mp hp')
      _ = _ := by simp
  by_contra! hlt
  have hc : ((primesThree (m^2)).card : ℝ) < m := by exact_mod_cast hlt
  nlinarith [mul_lt_mul_of_pos_right hc (show 0 < 2 * log (m:ℝ) by positivity),
    mul_le_mul_of_nonneg_left hlog hmpos.le]

/-- The uniform prime-product bound needed in the paper. The set has exactly m
distinct primes; for each m it may be taken inside a box of polynomial size. -/
theorem exists_prime_product_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m : ℕ, 2 ≤ m →
      ∃ P : Finset ℕ, P.card = m ∧ (∀ p ∈ P, p.Prime ∧ p % 4 = 3) ∧
        ((∏ p ∈ P, p : ℕ) : ℝ) ≤ exp (K * m * log m) := by
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp many_primes_three
  let B : ℕ := max m₀ 2
  have hB : 2 ≤ B := le_max_right _ _
  have hlog2 : 0 < log (2:ℝ) := log_pos (by norm_num)
  let K := 2 * (1 + log B / log 2)
  refine ⟨K, ?_, ?_⟩
  · have hbl : 0 ≤ log (B:ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
    dsimp [K]; nlinarith [div_nonneg hbl hlog2.le]
  intro m hm
  let M := max m B
  have hcount := hm₀ M (le_trans (le_max_left m₀ 2) (le_max_right m B))
  obtain ⟨P,hP,hcard⟩ := Finset.exists_subset_card_eq ((le_max_left m B).trans hcount)
  have hr (p) (hp : p ∈ P) := Finset.mem_filter.mp (hP hp)
  refine ⟨P,hcard,fun p hp => (hr p hp).2,?_⟩
  have hprod := Finset.prod_le_prod (s := P) (g := fun _ => M^2)
    (fun p hp => Finset.mem_Iic.mp (hr p hp).1)
  have hc : (∏ p ∈ P, p) ≤ (M^2)^m := by simpa [hcard] using hprod
  have hm1 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hB1 : 0 < (B:ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hM1 : 0 < (M:ℝ) := hm1.trans_le (by exact_mod_cast le_max_left m B)
  have hlog : log (M:ℝ) ≤ log (m:ℝ) + log (B:ℝ) := by
    rw [← Real.log_mul hm1.ne' hB1.ne']
    apply Real.log_le_log hM1
    exact_mod_cast (show M ≤ m*B from max_le
      (Nat.le_mul_of_pos_right _ (by omega)) (Nat.le_mul_of_pos_left _ (by omega)))
  have hlogm : log (2:ℝ) ≤ log (m:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  have hbl : 0 ≤ log (B:ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hBcost : log (B:ℝ) ≤ (log B / log 2) * log m := by
    calc
      _ = (log B / log 2) * log 2 := (div_mul_cancel₀ _ hlog2.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogm (div_nonneg hbl hlog2.le)
  calc
    _ ≤ ((M:ℝ)^2)^m := by exact_mod_cast hc
    _ = exp ((m:ℝ) * (2 * log M)) := by
      rw [Real.exp_nat_mul, show 2 * log (M:ℝ) = log ((M:ℝ)^2) by simp, Real.exp_log (by positivity)]
    _ ≤ _ := by
      apply exp_le_exp.mpr
      dsimp [K]
      nlinarith [mul_le_mul_of_nonneg_left (hlog.trans (add_le_add_right hBcost _)) hm1.le]

end RTS
