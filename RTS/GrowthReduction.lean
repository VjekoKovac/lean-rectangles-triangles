module

public import RTS.CombinatorialProof
public import Mathlib.Tactic

/-! The logarithmic choice of the number of prime factors at the end of §2.3. -/

@[expose] public section

namespace RTS

open Real Filter

/-- The prime-count parameter can be chosen at every large real scale. The caller supplies
the absolute double-exponential scale constant K and the prefactor a of the finite estimate. -/
theorem choosePrimeCount {K a : ℝ} (hK : 1 ≤ K) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℝ in atTop, ∃ m : ℕ, 2 ≤ m ∧
      exp (exp (K * m * log m)) ≤ N ∧
      logGrowth c N ≤ a * (4 / 3 : ℝ)^m := by
  let b := log (4 / 3 : ℝ)
  have hb : 0 < b := log_pos (by norm_num)
  have hK₀ : 0 < K := by linarith
  let H := max 4 (2 * (1 - log a / b))
  have hH : 0 < H := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left ..)
  let c := b / (2 * K)
  refine ⟨c, div_pos hb (by positivity), ?_⟩
  have hsmall := Real.isLittleO_log_id_atTop.bound (show 0 < 1 / (K * H) by positivity)
  have htlim : Tendsto (fun N : ℝ => log (log N)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_log_atTop
  filter_upwards [htlim.eventually hsmall, (tendsto_log_atTop.comp htlim).eventually_ge_atTop 1,
    htlim.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ)] with N hsmall hlll hll hN
  let t := log (log N)
  change 1 ≤ log t at hlll
  change 1 ≤ t at hll
  change ‖log t‖ ≤ 1 / (K * H) * ‖t‖ at hsmall
  rw [Real.norm_eq_abs, abs_of_pos (by linarith), Real.norm_eq_abs, abs_of_pos (by linarith),
    one_div_mul_eq_div] at hsmall
  have hlog : 0 < log t := by linarith
  have hKL : 0 < K * log t := mul_pos hK₀ hlog
  let z := t / (K * log t)
  have hHz : H ≤ z := by
    apply (le_div_iff₀ hKL).2
    calc
      H * (K * log t) = log t * (K * H) := by ring
      _ ≤ t := (le_div_iff₀ (mul_pos hK₀ hH)).1 hsmall
  have hz4 : 4 ≤ z := le_trans (le_max_left ..) hHz
  let m := ⌊z⌋₊
  have hm : (m : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hlt : z < (m : ℝ) + 1 := Nat.lt_floor_add_one z
  have hm2 : 2 ≤ m := by exact_mod_cast (show (2 : ℝ) ≤ m by linarith)
  have hzt : z ≤ t := div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le hK hlll)
  have hmt : log (m : ℝ) ≤ log t := log_le_log (by exact_mod_cast (show 0 < m by omega)) (hm.trans hzt)
  have hwindow : K * m * log m ≤ t := by
    calc
      K * m * log m ≤ K * m * log t := mul_le_mul_of_nonneg_left hmt (by positivity)
      _ = m * (K * log t) := by ring
      _ ≤ t := (le_div_iff₀ hKL).1 hm
  refine ⟨m, hm2, ?_, ?_⟩
  · calc
      exp (exp (K * m * log m)) ≤ exp (exp t) := exp_le_exp.mpr (exp_le_exp.mpr hwindow)
      _ = N := by simp [t, exp_log (log_pos hN), exp_log (lt_trans zero_lt_one hN)]
  · have hcost : 2 * (1 - log a / b) ≤ z := le_trans (le_max_right ..) hHz
    have hcost' : (1 - z / 2) * b ≤ log a := by
      apply (le_div_iff₀ hb).1
      linarith
    have hg : t * (c / log t) = z / 2 * b := by
      dsimp [c, z]
      ring
    rw [logGrowth, rpow_def_of_pos (log_pos hN)]
    change exp (t * (c / log t)) ≤ _
    rw [hg, ← exp_log ha, ← exp_log (by norm_num : (0 : ℝ) < 4/3) (x := (4/3 : ℝ))]
    rw [← exp_nat_mul, ← exp_add, exp_le_exp]
    change z / 2 * b ≤ log a + m * b
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) + 1 - z by linarith) hb.le]

/-- Assemble the two conclusions from the uniform fixed-modulus estimates after inserting
the prime-product upper bound. These two estimates are hypotheses of this reduction. -/
theorem growth_of_uniform_estimates {K a : ℝ} (hK : 1 ≤ K) (ha : 0 < a)
    (hbox : ∀ (m : ℕ), 2 ≤ m → ∀ N : ℝ, exp (exp (K * m * log m)) ≤ N →
      a * (4 / 3 : ℝ)^m ≤ pinnedBoxRatio N)
    (hsize : ∀ (m : ℕ), 2 ≤ m → ∀ n : ℕ, exp (exp (K * m * log m)) ≤ n →
      a * (4 / 3 : ℝ)^m ≤ pinnedSizeRatio n) : CombinatorialGrowth := by
  obtain ⟨c, hc, h⟩ := choosePrimeCount hK ha
  refine ⟨c, hc, ?_, ?_⟩
  · apply eventually_atTop.mp
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with N hN hN₀
    obtain ⟨m, hm, hW, hG⟩ := hN
    exact ⟨pinnedBoxRatio_le_boxRatio hN₀, hG.trans (hbox m hm N hW)⟩
  · have hn : ∀ᶠ n : ℕ in atTop, pinnedSizeRatio n ≤ sizeRatio n ∧
          logGrowth c n ≤ pinnedSizeRatio n := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop (1 : ℕ)]
        with n hN hn₀
      obtain ⟨m, hm, hW, hG⟩ := hN
      exact ⟨pinnedSizeRatio_le_sizeRatio hn₀, hG.trans (hsize m hm n hW)⟩
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hn
    exact ⟨n₀ + 1, by omega, fun n hN => hn₀ n (by omega)⟩

end RTS
