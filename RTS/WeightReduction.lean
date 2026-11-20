module

public import RTS.SmoothWeights
public import RTS.WeightApproximation

/-! Passing from the continuous-weight inequality to every weight of the paper. -/

@[expose] public section
noncomputable section
namespace RTS.Smoothing
open MeasureTheory Filter
open scoped ENNReal Topology

variable {d : ℕ}

private theorem wave_continuous (a : Freq d →₀ ℂ) :
    Continuous fun p : ST d => perWave a p.1 p.2 := by
  unfold perWave
  fun_prop

private theorem lhs_eq_pairing (a : Freq d →₀ ℂ) (w : ST d → ℝ) (hw : perWeight w) :
    perLHS a w =
      ∫⁻ z, ENNReal.ofReal (‖perWave a z.1 z.2‖^2) * ENNReal.ofReal (w z) ∂haar d := by
  have hm : Measurable (fun z : ST d => ENNReal.ofReal (‖perWave a z.1 z.2‖^2)) :=
    ENNReal.measurable_ofReal.comp ((wave_continuous a).norm.pow 2).measurable
  have hW : AEMeasurable (fun z => ENNReal.ofReal (w z)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hw.2.aestronglyMeasurable.aemeasurable
  simpa only [perLHS, ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm] using
    (lintegral_prod_symm (μ := torusMeasure d) (ν := circleMeasure)
      (fun z : ST d => ENNReal.ofReal (‖perWave a z.1 z.2‖^2) * ENNReal.ofReal (w z))
      (hm.aemeasurable.mul hW)).symm

theorem perAdmissible_of_continuous (kind : EstimateKind)
    (eligible : (Freq d →₀ ℂ) → Prop) (C : ℝ≥0∞)
    (h : ∀ a, eligible a → ∀ w, perWeight w → Continuous w →
      perLHS a w ≤ C * perRHS kind a w) : perAdmissible kind eligible C := by
  intro a ha w hw
  obtain ⟨v,hm,hv,hvw,he⟩ := measurable_minorant hw
  rw [← perLHS_congr_ae a he]
  apply le_trans _ (mul_le_mul_right (perRHS_mono kind a hvw) C)
  let H (z : ST d) := ‖perWave a z.1 z.2‖^2
  obtain ⟨K,hK,hpos,hMass,hLim⟩ := exists_approximation
    (H := H) (w := v) ((wave_continuous a).norm.pow 2) (fun _ => sq_nonneg _) hm hv.2
  rw [lhs_eq_pairing a v hv]
  apply le_of_tendsto hLim
  apply Eventually.of_forall
  intro n
  calc
    _ = perLHS a (regularize (K n) v) := by
      rw [lhs_eq_pairing _ _ (regularize_weight (hK n) (hpos n) hv)]
      simp only [regularize_ofReal (hK n) (hpos n) hv]
      rfl
    _ ≤ C * perRHS kind a (regularize (K n) v) :=
      h a ha _ (regularize_weight (hK n) (hpos n) hv) (regularize_continuous (hK n) hv)
    _ ≤ _ := mul_le_mul_right (regularize_rhs_le (hK n) (hpos n) (hMass n) hv hm kind a) C

end RTS.Smoothing
