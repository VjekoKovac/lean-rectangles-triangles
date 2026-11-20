module
public import RTS.AnalysisDefs
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Group.Prod
/-! Upper estimate in Theorem 1.5, for every finite support, including the empty support. -/
@[expose] public section
noncomputable section
namespace RTS
open MeasureTheory
open scoped ENNReal

theorem perWave_sq_le {d : ℕ} (a : Freq d →₀ ℂ) (x : Torus d) (t : UnitAddCircle) :
    ‖perWave a x t‖ₑ ^ 2 ≤ a.support.card * ∑ k ∈ a.support, ‖a k‖ₑ ^ 2 := by
  have hnorm : ‖perWave a x t‖ ≤ ∑ k ∈ a.support, ‖a k‖ := by
    unfold perWave
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro k _
    simp [UnitAddTorus.mFourier, fourier_apply, norm_prod]
  have hreal := (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (sq_sum_le_card_mul_sum_sq (s := a.support) (f := fun k => ‖a k‖))
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa [ENNReal.ofReal_mul, ENNReal.ofReal_sum_of_nonneg, ENNReal.ofReal_pow,
    ofReal_norm, sq_nonneg] using h

/-- The average over line intercepts is exactly the total mass of the weight. -/
theorem perXray_average {d : ℕ} (w : Torus d × UnitAddCircle → ℝ) (hw : perWeight w)
    (k : Freq d) :
    (∫⁻ x, perXray w x k ∂torusMeasure d) =
    ∫⁻ t, ∫⁻ x, ENNReal.ofReal (w (x,t)) ∂torusMeasure d ∂circleMeasure := by
  let g (t : UnitAddCircle) (x : Torus d) : Torus d := fun i => x i - (2 * k i) • t
  have trans (t : UnitAddCircle) : MeasurePreserving (g t) (torusMeasure d) (torusMeasure d) := by
    exact measurePreserving_sub_right _ (fun i => (2 * k i) • t)
  have skew := (MeasurePreserving.id circleMeasure).skew_product (g := g)
    (show Measurable (Function.uncurry g) from by
      apply Continuous.measurable
      apply continuous_pi
      intro i
      change Continuous (fun p : UnitAddCircle × Torus d => p.2 i - (2 * k i) • p.1)
      fun_prop)
    (Filter.Eventually.of_forall fun t => (trans t).map_eq)
  let W (p : Torus d × UnitAddCircle) := ENNReal.ofReal (w p)
  have hm : AEMeasurable W ((torusMeasure d).prod circleMeasure) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hw.2.aestronglyMeasurable.aemeasurable
  have mp : MeasurePreserving (fun p : UnitAddCircle × Torus d => (g p.1 p.2, p.1))
      (circleMeasure.prod (torusMeasure d)) ((torusMeasure d).prod circleMeasure) :=
    Measure.measurePreserving_swap.comp skew
  have hm' := hm.comp_quasiMeasurePreserving mp.quasiMeasurePreserving
  calc
    _ = ∫⁻ p : UnitAddCircle × Torus d, W (g p.1 p.2, p.1) ∂circleMeasure.prod (torusMeasure d) :=
      (lintegral_prod_symm _ hm').symm
    _ = ∫⁻ p, W p ∂(torusMeasure d).prod circleMeasure := by
      rw [← mp.map_eq] at hm ⊢
      exact lintegral_comp' hm mp.measurable.aemeasurable
    _ = _ := lintegral_prod_symm _ hm

theorem perSteinCard_le_card (d n : ℕ) : perSteinCard d n ≤ n := by
  apply sInf_le
  intro a ha w hw
  let B : ℝ≥0∞ := ∑ k ∈ a.support, ‖a k‖ₑ ^ 2
  let W : ℝ≥0∞ := ∫⁻ t, ∫⁻ x, ENNReal.ofReal (w (x,t)) ∂torusMeasure d ∂circleMeasure
  have hb : B ≠ ⊤ := by simp [B]
  have hc : (n : ℝ≥0∞) * B ≠ ⊤ := ENNReal.mul_ne_top (by simp) hb
  have ray (k : Freq d) : W ≤ ⨆ x, perXray w x k := by
    rw [show W = ∫⁻ x, perXray w x k ∂torusMeasure d from (perXray_average w hw k).symm]
    calc
      _ ≤ ∫⁻ _ : Torus d, ⨆ x, perXray w x k ∂torusMeasure d :=
        lintegral_mono fun x => le_iSup (fun z => perXray w z k) x
      _ = _ := by simp
  calc
    perLHS a w ≤ ∫⁻ t, ∫⁻ x, ((n : ℝ≥0∞) * B) * ENNReal.ofReal (w (x,t))
        ∂torusMeasure d ∂circleMeasure := by
      apply lintegral_mono; intro t; apply lintegral_mono; intro x
      exact mul_le_mul_left (by simpa only [ha] using perWave_sq_le a x t) _
    _ = (n : ℝ≥0∞) * (B * W) := by
      simp_rw [lintegral_const_mul' _ _ hc]
      exact mul_assoc _ _ _
    _ ≤ _ := by
      apply mul_le_mul_right
      unfold B
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_right (ray k) _

end RTS
