module

public import RTS.Configuration
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity

/-! The test function with unit coefficients on A and the test weight |u_A|².
This reduces a bound for each ratio to the classical character integrals
in Section 4. -/

@[expose] public section

namespace RTS.Configuration

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

def configCoeff (A : Finset Point) : Point →₀ ℂ :=
  Finsupp.indicator A (fun _ _ => 1)

@[simp] theorem configCoeff_support (A : Finset Point) : (configCoeff A).support = A := by
  classical
  ext k
  simp [configCoeff, Finsupp.mem_support_iff, Finsupp.indicator_apply]

@[simp] theorem configCoeff_mem {A : Finset Point} {k : Point} (hk : k ∈ A) :
    configCoeff A k = 1 := by
  simp [configCoeff, Finsupp.indicator_apply, hk]

theorem perWave_configCoeff (A : Finset Point) (x : Torus 2) (t : UnitAddCircle) :
    perWave (configCoeff A) x t = configWave A x t := by
  simp only [perWave, configWave, configCoeff_support]
  exact Finset.sum_congr rfl fun k hk => by rw [configCoeff_mem hk, one_mul]

def configWeight (A : Finset Point) (z : Torus 2 × UnitAddCircle) : ℝ :=
  ‖configWave A z.1 z.2‖ ^ 2

@[fun_prop] theorem configWave_continuous (A : Finset Point) :
    Continuous (fun z : Torus 2 × UnitAddCircle => configWave A z.1 z.2) := by
  unfold configWave
  fun_prop

theorem configWeight_valid (A : Finset Point) : perWeight (configWeight A) := by
  refine ⟨fun z => sq_nonneg _, ?_⟩
  exact ((configWave_continuous A).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem configLHS (A : Finset Point) :
    perLHS (configCoeff A) (configWeight A) =
    ENNReal.ofReal (∫ t, ∫ x, ‖configWave A x t‖ ^ 4 ∂torusMeasure 2 ∂circleMeasure) := by
  let F (z : UnitAddCircle × Torus 2) : ℝ := ‖configWave A z.2 z.1‖ ^ 4
  have hF : Continuous F := ((configWave_continuous A).comp continuous_swap).norm.pow 4
  have hI : Integrable F (circleMeasure.prod (torusMeasure 2)) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : 0 ≤ᵐ[circleMeasure.prod (torusMeasure 2)] F :=
    Filter.Eventually.of_forall fun z => pow_nonneg (norm_nonneg _) 4
  rw [← integral_prod F hI, ofReal_integral_eq_lintegral_ofReal hI h0,
    lintegral_prod (fun z => ENNReal.ofReal (F z)) (ENNReal.continuous_ofReal.comp hF).aemeasurable]
  unfold perLHS configWeight F
  simp only [perWave_configCoeff, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
    ← pow_add]

theorem configXray_le (A : Finset Point)
    (hp : ∀ (x : Torus 2) (k : Point), (∫ t, ‖configWave A (fun i => x i - (2 * k i) • t) t‖ ^ 2
       ∂circleMeasure) ≤ pinnedTriangleCount A k)
    (x : Torus 2) (k : Point) :
    perXray (configWeight A) x k ≤ pinnedTriangleCount A k := by
  let g (t : UnitAddCircle) : ℝ := ‖configWave A (fun i => x i - (2 * k i) • t) t‖ ^ 2
  have hline : Continuous (fun t : UnitAddCircle => (fun i => x i - (2 * k i) • t : Torus 2)) :=
    continuous_pi fun i => continuous_const.sub (continuous_zsmul (2 * k i))
  have hc : Continuous g := (((configWave_continuous A).comp
    (hline.prodMk continuous_id)).norm).pow 2
  have hi : Integrable g circleMeasure := hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  change (∫⁻ t, ENNReal.ofReal (g t) ∂circleMeasure) ≤ _
  have hnonneg : 0 ≤ᵐ[circleMeasure] g := Filter.Eventually.of_forall fun _ => sq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg]
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hp x k)

private theorem ratio_bound (r s : ℕ) (C : ℝ≥0∞) (h : (r : ℝ≥0∞) ≤ C * s) :
    ENNReal.ofReal ((r : ℝ) / s) ≤ C := by
  by_cases hs : s = 0
  · simp [hs]
  have hs₁ : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  rw [ENNReal.ofReal_div_of_pos hs₁, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  exact (ENNReal.div_le_iff (by exact_mod_cast hs) (by simp)).2 h

theorem ratio_le_perBest (A : Finset Point) (eligible : (Point →₀ ℂ) → Prop)
    (he : eligible (configCoeff A))
    (hr : (∫ t, ∫ x, ‖configWave A x t‖ ^ 4 ∂torusMeasure 2 ∂circleMeasure) = rectangleCount A)
    (hp : ∀ (x : Torus 2) (k : Point), (∫ t, ‖configWave A (fun i => x i - (2 * k i) • t) t‖ ^ 2
       ∂circleMeasure) ≤ pinnedTriangleCount A k) :
    ENNReal.ofReal (ratio A) ≤ perBest .stein eligible := by
  apply le_sInf
  intro C hC
  have h := hC (configCoeff A) he (configWeight A) (configWeight_valid A)
  rw [configLHS, hr, ENNReal.ofReal_natCast] at h
  apply ratio_bound
  apply h.trans
  apply mul_le_mul_right
  simp only [perRHS, configCoeff_support, triangleCount, Nat.cast_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  simpa [configCoeff_mem hk] using iSup_le (fun x => configXray_le A hp x k)

theorem pinnedRatio_le_perBest (A : Finset Point) (eligible : (Point →₀ ℂ) → Prop)
    (he : eligible (configCoeff A))
    (hr : (∫ t, ∫ x, ‖configWave A x t‖ ^ 4 ∂torusMeasure 2 ∂circleMeasure) = rectangleCount A)
    (hp : ∀ (x : Torus 2) (k : Point), (∫ t, ‖configWave A (fun i => x i - (2 * k i) • t) t‖ ^ 2
       ∂circleMeasure) ≤ pinnedTriangleCount A k) :
    ENNReal.ofReal (pinnedRatio A) ≤ perBest .mt eligible := by
  apply le_sInf
  intro C hC
  have h := hC (configCoeff A) he (configWeight A) (configWeight_valid A)
  rw [configLHS, hr, ENNReal.ofReal_natCast] at h
  apply ratio_bound
  apply h.trans
  apply mul_le_mul_right
  simp only [perRHS, configCoeff_support, Nat.cast_mul]
  have hs : (∑ k ∈ A, ‖configCoeff A k‖ₑ ^ 2) = (A.card : ℝ≥0∞) := by
    calc
      _ = ∑ _k ∈ A, (1 : ℝ≥0∞) := Finset.sum_congr rfl
        (fun k hk => by simp [configCoeff_mem hk])
      _ = _ := by simp
  rw [hs]
  apply mul_le_mul_right
  refine iSup_le fun k => iSup_le fun x => (configXray_le A hp x k).trans ?_
  have hk : (k : Point) ∈ A := by simpa only [configCoeff_support] using k.property
  exact_mod_cast (Finset.le_sup (f := pinnedTriangleCount A) hk)

end
end RTS.Configuration
