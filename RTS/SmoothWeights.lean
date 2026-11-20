module

public import RTS.AnalysisDefs
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Group.Measure

/-! The smoothing reduction in Section 3. We work with actual representatives of weights.
A measurable pointwise minorant preserves the left side and can only decrease the ray
integrals. Convolution with a nonnegative probability density averages translated rays. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology Convolution

namespace RTS.Smoothing

abbrev ST (d : ℕ) := Torus d × UnitAddCircle
abbrev haar (d : ℕ) := (torusMeasure d).prod circleMeasure

variable {d : ℕ}
local instance : ((torusMeasure d).prod circleMeasure).IsAddLeftInvariant :=
  Measure.prod.instIsAddLeftInvariant (μ := torusMeasure d) (ν := circleMeasure)
local instance : ((torusMeasure d).prod circleMeasure).IsAddRightInvariant :=
  Measure.prod.instIsAddRightInvariant (μ := torusMeasure d) (ν := circleMeasure)
local instance : MeasurableAdd (ST d) := ContinuousAdd.measurableAdd
local instance : ((torusMeasure d).prod circleMeasure).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (μ := torusMeasure d) (ν := circleMeasure)


local instance : ((torusMeasure d).prod circleMeasure).IsNegInvariant := by
  have circ := Measure.measurePreserving_neg circleMeasure
  have spatial : MeasurePreserving Neg.neg (torusMeasure d) (torusMeasure d) :=
    measurePreserving_pi (fun _ : Fin d => circleMeasure) (fun _ : Fin d => circleMeasure)
      (fun _ => circ)
  exact ⟨(spatial.prod circ).map_eq⟩

theorem measurable_minorant {w : ST d → ℝ} (hw : perWeight w) :
    ∃ v : ST d → ℝ, Measurable v ∧ perWeight v ∧ v ≤ w ∧ v =ᵐ[haar d] w := by
  have hm := hw.2.aestronglyMeasurable.aemeasurable
  classical
  obtain ⟨s,hs,hsmeas,hsnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hm.ae_eq_mk)
  let v := sᶜ.indicator (hm.mk w)
  have hv (x) (hx : x ∉ s) : v x = w x := by
    have heq : w x = hm.mk w x := by by_contra h; exact hx (hs h)
    simp [v,hx,heq]
  have hv0 (x) (hx : x ∈ s) : v x = 0 := by simp [v,hx]
  have hcom : ∀ᵐ x ∂haar d, x ∉ s := by
    change sᶜ ∈ ae (haar d)
    exact compl_mem_ae_iff.mpr hsnull
  have he : v =ᵐ[haar d] w := hcom.mono fun x hx => hv x hx
  exact ⟨v,hm.measurable_mk.indicator hsmeas.compl,
    ⟨fun x => by by_cases hx : x ∈ s <;> simp [hv0,hv,hx,hw.1],
     hw.2.congr he.symm⟩,
    fun x => by by_cases hx : x ∈ s <;> simp [hv0,hv,hx,hw.1],he⟩

theorem perLHS_congr_ae (a : Freq d →₀ ℂ) {v w : ST d → ℝ}
    (h : v =ᵐ[haar d] w) : perLHS a v = perLHS a w := by
  apply lintegral_congr_ae
  have he : (v ∘ Prod.swap) =ᵐ[circleMeasure.prod (torusMeasure d)] (w ∘ Prod.swap) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [Measure.ae_ae_eq_curry_of_prod he] with t ht
  apply lintegral_congr_ae
  filter_upwards [ht] with x hx
  rw [show v (x,t) = w (x,t) from hx]

theorem perRHS_mono (kind : EstimateKind) (a : Freq d →₀ ℂ) {v w : ST d → ℝ}
    (h : v ≤ w) : perRHS kind a v ≤ perRHS kind a w := by
  have ray (k : Freq d) (x : Torus d) : perXray v x k ≤ perXray w x k :=
    lintegral_mono fun t => ENNReal.ofReal_le_ofReal (h _)
  cases kind with
  | stein =>
    exact Finset.sum_le_sum fun k _ => mul_le_mul_right (iSup_mono (ray k)) _
  | mt => exact mul_le_mul_right (iSup_mono fun k : ↥a.support => iSup_mono (ray k)) _

def rayPoint (x : Torus d) (k : Freq d) (t : UnitAddCircle) : ST d :=
  (fun i => x i - (2 * k i) • t, t)

theorem rayPoint_sub (x : Torus d) (k : Freq d) (y : ST d) (t : UnitAddCircle) :
    rayPoint x k t - y =
      rayPoint (fun i => x i - y.1 i - (2 * k i) • y.2) k (t - y.2) := by
  ext i
  · change x i - (2 * k i) • t - y.1 i = (x i - y.1 i - (2 * k i) • y.2) - (2 * k i) • (t - y.2)
    rw [smul_sub]
    generalize (2 * k i) • t = b
    generalize (2 * k i) • y.2 = c
    abel
  · rfl

theorem translated_ray (w : ST d → ℝ) (x : Torus d) (k : Freq d) (y : ST d) :
    (∫⁻ t, ENNReal.ofReal (w (rayPoint x k t - y)) ∂circleMeasure) =
      perXray w (fun i => x i - y.1 i - (2 * k i) • y.2) k := by
  simp_rw [rayPoint_sub]
  exact lintegral_sub_right_eq_self (fun t => ENNReal.ofReal (w (rayPoint _ k t))) y.2

/-- Probability convolution written in extended nonnegative reals. -/
def rayAverage (K w : ST d → ℝ) (z : ST d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (K y) * ENNReal.ofReal (w (z-y)) ∂haar d

theorem averaged_ray_le {K w : ST d → ℝ} (hK : Measurable K) (hw : Measurable w)
    (hOne : (∫⁻ y, ENNReal.ofReal (K y) ∂haar d) = 1) (x : Torus d) (k : Freq d) :
    (∫⁻ t, rayAverage K w (rayPoint x k t) ∂circleMeasure) ≤ ⨆ x, perXray w x k := by
  have hc : Continuous (rayPoint x k) := by
    unfold rayPoint
    apply Continuous.prodMk _ continuous_id
    apply continuous_pi
    intro i
    fun_prop
  unfold rayAverage
  rw [lintegral_lintegral_swap (by
    exact (ENNReal.measurable_ofReal.comp (hK.comp measurable_snd)).mul
      (ENNReal.measurable_ofReal.comp (hw.comp (((hc.comp continuous_fst).sub continuous_snd).measurable))) |>.aemeasurable)]
  calc
    _ = ∫⁻ y, ENNReal.ofReal (K y) * perXray w
        (fun i => x i - y.1 i - (2 * k i) • y.2) k ∂haar d := by
      apply lintegral_congr
      intro y
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, translated_ray]
    _ ≤ ∫⁻ y, ENNReal.ofReal (K y) * (⨆ z, perXray w z k) ∂haar d :=
      lintegral_mono fun y => mul_le_mul_right (le_iSup (fun z => perXray w z k) _) _
    _ = _ := by
      have H : Measurable (fun y => ENNReal.ofReal (K y)) := ENNReal.measurable_ofReal.comp hK
      rw [lintegral_mul_const _ H, hOne, one_mul]

/-- Convolution on the product Haar probability space. -/
def regularize (K w : ST d → ℝ) (z : ST d) : ℝ :=
  ∫ y, K y * w (z-y) ∂haar d

theorem regularize_continuous {K w : ST d → ℝ} (hK : Continuous K) (hw : perWeight w) :
    Continuous (regularize K w) :=
  (HasCompactSupport.of_compactSpace K).continuous_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hK hw.2.locallyIntegrable

theorem regularize_weight {K w : ST d → ℝ} (hK : Continuous K) (hpos : ∀ z, 0 ≤ K z)
    (hw : perWeight w) : perWeight (regularize K w) :=
  ⟨fun _z => integral_nonneg fun y => mul_nonneg (hpos y) (hw.1 _),
    (regularize_continuous hK hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)⟩

theorem regularize_ofReal {K w : ST d → ℝ} (hK : Continuous K) (hpos : ∀ z, 0 ≤ K z)
    (hw : perWeight w) (z : ST d) : ENNReal.ofReal (regularize K w z) = rayAverage K w z := by
  have hi : Integrable (fun y => K y * w (z-y)) (haar d) :=
    (HasCompactSupport.of_compactSpace K).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) hK hw.2.locallyIntegrable z
  rw [regularize, ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun y => mul_nonneg (hpos y) (hw.1 _))]
  simp only [rayAverage, ENNReal.ofReal_mul (hpos _)]

theorem regularize_rhs_le {K w : ST d → ℝ} (hK : Continuous K) (hpos : ∀ z, 0 ≤ K z)
    (hOne : (∫⁻ y, ENNReal.ofReal (K y) ∂haar d) = 1) (hw : perWeight w) (hm : Measurable w)
    (kind : EstimateKind) (a : Freq d →₀ ℂ) : perRHS kind a (regularize K w) ≤ perRHS kind a w := by
  have ray (k : Freq d) : (⨆ x, perXray (regularize K w) x k) ≤ ⨆ x, perXray w x k := by
    apply iSup_le
    intro x
    change (∫⁻ t, ENNReal.ofReal (regularize K w (rayPoint x k t)) ∂circleMeasure) ≤ _
    simp_rw [regularize_ofReal hK hpos hw]
    exact averaged_ray_le hK.measurable hm hOne x k
  cases kind with
  | stein => exact Finset.sum_le_sum fun k _ => mul_le_mul_right (ray k) _
  | mt => exact mul_le_mul_right (iSup_mono fun k : ↥a.support => ray k) _

end RTS.Smoothing
