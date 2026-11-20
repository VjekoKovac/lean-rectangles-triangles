module

public import RTS.AnalysisDefs
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Continuous approximate identities on the spacetime torus
Pairing with a continuous test function reduces the claim to continuity of its
translations in the finite measure with density w. -/
@[expose] public section
noncomputable section

open MeasureTheory Filter Set Function
open scoped ENNReal Topology Convolution
namespace RTS.Smoothing

private abbrev X (d : ℕ) := Torus d × UnitAddCircle
private abbrev μ (d : ℕ) := (torusMeasure d).prod circleMeasure
variable {d : ℕ}

local instance : ((torusMeasure d).prod circleMeasure).IsAddLeftInvariant :=
  Measure.prod.instIsAddLeftInvariant (μ := torusMeasure d) (ν := circleMeasure)
local instance : ((torusMeasure d).prod circleMeasure).IsAddRightInvariant :=
  Measure.prod.instIsAddRightInvariant (μ := torusMeasure d) (ν := circleMeasure)
local instance : MeasurableAdd (Torus d × UnitAddCircle) := ContinuousAdd.measurableAdd

private theorem exists_tent (r : ℝ) (hr : 0 < r) :
    ∃ K : X d → ℝ, Continuous K ∧ (∀ z, 0 ≤ K z) ∧
      (∫ z, K z ∂μ d) = 1 ∧ support K ⊆ Metric.ball 0 r := by
  let f (z : X d) := max 0 (r - dist z 0)
  have hf : Continuous f := by unfold f; fun_prop
  have hnon (z) : 0 ≤ f z := le_max_left .. 
  have hi := hf.integrable_of_hasCompactSupport (μ := μ d) (HasCompactSupport.of_compactSpace _)
  have hpos : 0 < ∫ z, f z ∂μ d := integral_pos_of_integrable_nonneg_nonzero hf hi hnon
    (show f 0 ≠ 0 by simp [f, max_eq_right hr.le, hr.ne'])
  refine ⟨fun z => (∫ x, f x ∂μ d)⁻¹ * f z, continuous_const.mul hf,
    fun z => mul_nonneg (inv_nonneg.mpr hpos.le) (hnon _), ?_, ?_⟩
  · rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']
  · intro z hz
    by_contra h
    have hdist : r ≤ dist z 0 := le_of_not_gt (fun hlt => h (Metric.mem_ball.mpr hlt))
    exact hz (by simp only [f, max_eq_left (sub_nonpos.mpr hdist), mul_zero])

private theorem integral_identity {K H w : X d → ℝ} (hK : Continuous K) (hK₀ : ∀ z, 0 ≤ K z)
    (hH : Continuous H) (hH₀ : ∀ z, 0 ≤ H z) (hw : Measurable w) (hiw : Integrable w (μ d)) :
    (∫⁻ z, ENNReal.ofReal (H z) * (∫⁻ y, ENNReal.ofReal (K y) * ENNReal.ofReal (w (z-y)) ∂μ d) ∂μ d) =
    ENNReal.ofReal (∫ y, K y * (∫ z, H (z+y) ∂(μ d).withDensity (fun z => ENNReal.ofReal (w z))) ∂μ d) := by
  let ν := (μ d).withDensity (fun z => ENNReal.ofReal (w z))
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hiw.2
  have hB : Continuous (fun y => ∫ z, H (z+y) ∂ν) := by
    apply Continuous.congr (f := fun y => ∫ z in (univ : Set (X d)), H (z+y) ∂ν)
    · apply continuous_parametric_integral_of_continuous _ isCompact_univ
      fun_prop
    · simp
  have conv (y : X d) :
      (∫⁻ z, ENNReal.ofReal (H z) * ENNReal.ofReal (w (z-y)) ∂μ d) =
      ENNReal.ofReal (∫ z, H (z+y) ∂ν) := by
    have fcont : Continuous (fun z : X d => H (z+y)) := by fun_prop
    rw [ofReal_integral_eq_lintegral_ofReal
      (fcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Eventually.of_forall fun z => hH₀ (z+y))]
    dsimp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul (μ d) (f := fun z => ENNReal.ofReal (w z))
      (g := fun z => ENNReal.ofReal (H (z+y))) (ENNReal.measurable_ofReal.comp hw)
      (ENNReal.measurable_ofReal.comp fcont.measurable)]
    have tr := lintegral_add_right_eq_self (μ := μ d)
      (fun z : X d => ENNReal.ofReal (H z) * ENNReal.ofReal (w (z-y))) y
    simpa [mul_comm] using tr.symm
  have houter : Integrable (fun y => K y * ∫ z, H (z+y) ∂(μ d).withDensity (fun z => ENNReal.ofReal (w z))) (μ d) := (hK.mul hB).integrable_of_hasCompactSupport (μ := μ d) (HasCompactSupport.of_compactSpace _)
  have hge : ∀ y, 0 ≤ ∫ z, H (z+y) ∂ν := fun _ => integral_nonneg (fun _ => hH₀ _)
  rw [ofReal_integral_eq_lintegral_ofReal houter
    (Eventually.of_forall fun y => mul_nonneg (hK₀ y) (hge y))]
  simp_rw [ENNReal.ofReal_mul (hK₀ _)]
  change _ = ∫⁻ y, ENNReal.ofReal (K y) * ENNReal.ofReal (∫ z, H (z+y) ∂ν) ∂μ d
  simp_rw [← conv]
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr; intro y; apply lintegral_congr; intro z; ac_rfl
  · apply Measurable.aemeasurable
    have hs : Measurable (fun p : X d × X d => p.1 - p.2) :=
      (measurable_fst.fst.sub measurable_snd.fst).prodMk (measurable_fst.snd.sub measurable_snd.snd)
    exact (ENNReal.measurable_ofReal.comp (hH.measurable.comp measurable_fst)).mul
      ((ENNReal.measurable_ofReal.comp (hK.measurable.comp measurable_snd)).mul
       (ENNReal.measurable_ofReal.comp (hw.comp hs)))

theorem exists_approximation {H w : Torus d × UnitAddCircle → ℝ}
    (hH : Continuous H) (hH₀ : ∀ z, 0 ≤ H z) (hw : Measurable w)
    (hiw : Integrable w ((torusMeasure d).prod circleMeasure)) :
    ∃ K : ℕ → Torus d × UnitAddCircle → ℝ,
      (∀ n, Continuous (K n)) ∧ (∀ n z, 0 ≤ K n z) ∧
      (∀ n, (∫⁻ y, ENNReal.ofReal (K n y) ∂(torusMeasure d).prod circleMeasure) = 1) ∧
      Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (H z) *
        (∫⁻ y, ENNReal.ofReal (K n y) * ENNReal.ofReal (w (z-y)) ∂(torusMeasure d).prod circleMeasure)
        ∂(torusMeasure d).prod circleMeasure) atTop
        (𝓝 (∫⁻ z, ENNReal.ofReal (H z) * ENNReal.ofReal (w z) ∂(torusMeasure d).prod circleMeasure)) := by
  choose K hK hK₀ hK₁ hKs using fun n : ℕ => exists_tent (d := d) (1/(n+1:ℝ)) (by positivity)
  refine ⟨K, hK, hK₀, fun n => ?_, ?_⟩
  · rw [← ofReal_integral_eq_lintegral_ofReal
      ((hK n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Eventually.of_forall (hK₀ n)), hK₁, ENNReal.ofReal_one]
  let ν := (μ d).withDensity (fun z => ENNReal.ofReal (w z))
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hiw.2
  let B (s : X d) := ∫ z, H (z-s) ∂ν
  have hB : Continuous B := by
    unfold B
    apply Continuous.congr (f := fun y => ∫ z in (univ : Set (X d)), H (z-y) ∂ν)
    · apply continuous_parametric_integral_of_continuous _ isCompact_univ
      fun_prop
    · simp
  have hsmall : Tendsto (fun n => support (K n)) atTop (𝓝 0).smallSets := by
    rw [tendsto_smallSets_iff]
    intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    filter_upwards [ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hε] with n hn
    exact (hKs n).trans ((Metric.ball_subset_ball hn.le).trans hball)
  have hh := convolution_tendsto_right (μ := μ d) (g := fun _ : ℕ => B) (x₀ := 0)
    (φ := K) (k := fun _ : ℕ => (0 : X d)) (Eventually.of_forall hK₀)
    (Eventually.of_forall hK₁) hsmall (Eventually.of_forall fun _ => hB.aestronglyMeasurable)
    (hB.continuousAt.tendsto.comp tendsto_snd) tendsto_const_nhds
  have he : ENNReal.ofReal (B 0) = ∫⁻ z, ENNReal.ofReal (H z) * ENNReal.ofReal (w z) ∂μ d := by
    simp only [B, sub_zero]
    rw [ofReal_integral_eq_lintegral_ofReal
      (hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Eventually.of_forall hH₀)]
    dsimp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul (μ d) (f := fun z => ENNReal.ofReal (w z))
      (g := fun z => ENNReal.ofReal (H z)) (ENNReal.measurable_ofReal.comp hw)
      (ENNReal.measurable_ofReal.comp hH.measurable)]
    simp [mul_comm]
  rw [← he]
  simp_rw [integral_identity (hK _) (hK₀ _) hH hH₀ hw hiw]
  simpa [MeasureTheory.convolution, B, ν, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh

end RTS.Smoothing
end
