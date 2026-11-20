module

public import RTS.Transference
public import RTS.PacketBox
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Normalization and limits of the rectangular frequency packets -/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators Pointwise

namespace RTS.Transference

variable {d : ℕ}

/-- The closed unit cube differs from the half-open integration cell by a null set. -/
def unitBox (d : ℕ) : Set (Space d) := Icc 0 (fun _ => 1)

theorem volume_unitBox : volume (unitBox d) = 1 := by
  simp [unitBox, Real.volume_Icc_pi]

/-- Integration against the pushforward of the unit cube probability measure
by `y ↦ r • y`. For positive `r` it is the normalized average over the radius-`r` box. -/
def boxAverage (r : ℝ) (f : Space d → ℝ) : ℝ :=
  ∫ y in unitBox d, f (r • y)

theorem boxAverage_zero (f : Space d → ℝ) : boxAverage 0 f = f 0 := by
  simp [boxAverage, measureReal_def, volume_unitBox]

theorem boxAverage_nonneg {f : Space d → ℝ} (hf : ∀ z, 0 ≤ f z) (r : ℝ) :
    0 ≤ boxAverage r f := integral_nonneg fun _ => hf _

theorem originBox_mul (r : ℝ) (hr : 0 < r) :
    r • originBox d 1 = originBox d r := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  simp only [originBox, Set.mem_univ_pi, Set.mem_Ioc, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h i
    obtain ⟨h₁,h₂⟩ := h i
    constructor
    · exact (mul_pos_iff_of_pos_left (inv_pos.mpr hr)).1 h₁
    · calc z i = r * (r⁻¹ * z i) := by field_simp
           _ ≤ r * 1 := mul_le_mul_of_nonneg_left h₂ hr.le
           _ = _ := mul_one _
  · intro h i
    exact ⟨mul_pos (inv_pos.mpr hr) (h i).1,
      (mul_le_mul_of_nonneg_left (h i).2 (inv_nonneg.mpr hr.le)).trans
        (by rw [inv_mul_cancel₀ hr.ne'])⟩

/-- The exact (r^d) factor is common to the two sides of transference. -/
theorem integral_originBox (r : ℝ) (hr : 0 < r) (f : Space d → ℝ) :
    (∫ η in originBox d r, f η) = r^d * boxAverage r f := by
  have he : originBox d 1 =ᵐ[volume] unitBox d :=
    Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Space d)) f
    (originBox d 1) hr
  rw [originBox_mul r hr, setIntegral_congr_set he] at h
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul] at h
  unfold boxAverage
  rw [h]
  field_simp

/-- Real representative of a torus weight, before truncation in time. -/
def weightValue (w : Torus d × UnitAddCircle → ℝ) (p : Space d × ℝ) : ℝ :=
  w (fun i => (p.1 i : UnitAddCircle), (p.2 : UnitAddCircle))

theorem weightValue_continuous {w : Torus d × UnitAddCircle → ℝ} (hw : Continuous w) :
    Continuous (weightValue w) := by
  apply hw.comp
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' 1).comp ((continuous_apply i).comp continuous_fst)
  · exact (AddCircle.continuous_mk' 1).comp continuous_snd

/-- Weighted energy per unit packet mass, in fixed normalized variables. -/
def cellEnergy (a : Freq d →₀ ℂ) (w : Torus d × UnitAddCircle → ℝ) (r : ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, ∫ x in unitBox d,
    boxAverage r (fun η => ‖shiftedWave a (x,t) η‖^2) * weightValue w (x,t)

theorem cellEnergy_continuous (a : Freq d →₀ ℂ) {w : Torus d × UnitAddCircle → ℝ}
    (hw : Continuous w) : Continuous (cellEnergy a w) := by
  have h₁ : Continuous (fun q : (ℝ × ℝ) × Space d =>
      boxAverage q.1.1 (fun η => ‖shiftedWave a (q.2,q.1.2) η‖^2)) := by
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    change Continuous (fun q : ((ℝ × ℝ) × Space d) × Space d =>
      ‖shiftedWave a (q.1.2,q.1.1.2) (q.1.1.1 • q.2)‖^2)
    exact ((shiftedWave_continuous a).comp
      (((continuous_snd.comp continuous_fst).prodMk
          (continuous_snd.comp (continuous_fst.comp continuous_fst))).prodMk
        ((continuous_fst.comp (continuous_fst.comp continuous_fst)).smul continuous_snd))).norm.pow 2
  have h₂ : Continuous (fun q : ℝ × ℝ => ∫ x in unitBox d,
      boxAverage q.1 (fun η => ‖shiftedWave a (x,q.2) η‖^2) * weightValue w (x,q.2)) :=
    continuous_parametric_integral_of_continuous (h₁.mul ((weightValue_continuous hw).comp
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))) isCompact_Icc
  exact continuous_parametric_integral_of_continuous h₂ isCompact_Icc

theorem cellEnergy_zero (a : Freq d →₀ ℂ) (w : Torus d × UnitAddCircle → ℝ) :
    cellEnergy a w 0 = ∫ t in Icc (0:ℝ) 1, ∫ x in unitBox d,
      ‖perWave a (fun i => (x i : UnitAddCircle)) (t : UnitAddCircle)‖^2 * weightValue w (x,t) := by
  simp [cellEnergy, boxAverage_zero, shiftedWave_zero]

theorem integral_packet_energy (a : Freq d →₀ ℂ) (w : Torus d × UnitAddCircle → ℝ)
    (r : ℝ) (hr : 0 < r) :
    (∫ t in Icc (0:ℝ) 1, ∫ x in unitBox d,
      (∫ η in originBox d r, ‖shiftedWave a (x,t) η‖^2) * weightValue w (x,t)) =
      r^d * cellEnergy a w r := by
  simp only [integral_originBox r hr, cellEnergy, mul_assoc, integral_const_mul]

/-- A radius-`r` velocity average in each packet, weighted by its squared coefficient. -/
def steinAverage (a : Freq d →₀ ℂ) (X : Space d → ℝ) (r : ℝ) : ℝ :=
  ∑ k ∈ a.support, ‖a k‖^2 * boxAverage r (fun η => X ((fun i => (k i : ℝ)) + η))

theorem steinAverage_continuous (a : Freq d →₀ ℂ) {X : Space d → ℝ}
    (hX : Continuous X) : Continuous (steinAverage a X) := by
  unfold steinAverage
  apply continuous_finsetSum
  intro k _
  apply Continuous.const_mul
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  exact hX.comp (continuous_const.add (continuous_fst.smul continuous_snd))

theorem steinAverage_zero (a : Freq d →₀ ℂ) (X : Space d → ℝ) :
    steinAverage a X 0 = ∑ k ∈ a.support, ‖a k‖^2 * X (fun i => (k i : ℝ)) := by
  simp [steinAverage, boxAverage_zero]



/-- Maximum of a continuous velocity cost on the union of the closed packets.
The closed faces ensure this envelope also bounds the essential closed support. -/
def mtEnvelope (a : Freq d →₀ ℂ) (X : Space d → ℝ) (r : ℝ) : ℝ :=
  sSup ((fun p : a.support × unitBox d =>
    X ((fun i => ((p.1 : Freq d) i : ℝ)) + r • (p.2 : Space d))) '' univ)

private theorem continuous_packet_cost (a : Freq d →₀ ℂ) {X : Space d → ℝ}
    (hX : Continuous X) :
    Continuous (fun q : ℝ × (a.support × unitBox d) =>
      X ((fun i => ((q.2.1 : Freq d) i : ℝ)) + q.1 • (q.2.2 : Space d))) := by
  have hk : Continuous (fun k : a.support => (fun i => ((k : Freq d) i : ℝ)) : ↥a.support → Space d) :=
    continuous_of_discreteTopology
  exact hX.comp ((hk.comp (continuous_fst.comp continuous_snd)).add
    (continuous_fst.smul (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))

theorem mtEnvelope_continuous (a : Freq d →₀ ℂ) {X : Space d → ℝ}
    (hX : Continuous X) : Continuous (mtEnvelope a X) := by
  let : CompactSpace (unitBox d) := isCompact_iff_compactSpace.mp isCompact_Icc
  exact isCompact_univ.continuous_sSup (continuous_packet_cost a hX)

theorem cost_le_mtEnvelope (a : Freq d →₀ ℂ) {X : Space d → ℝ} (hX : Continuous X)
    {r : ℝ} (hr : 0 < r) {k : Freq d} (hk : k ∈ a.support) {v : Space d}
    (hv : ∀ i, v i - (k i : ℝ) ∈ Icc 0 r) :
    X v ≤ mtEnvelope a X r := by
  let : CompactSpace (unitBox d) := isCompact_iff_compactSpace.mp isCompact_Icc
  let y : Space d := fun i => (v i - (k i : ℝ)) / r
  have hy : y ∈ unitBox d :=
    ⟨fun i => div_nonneg (hv i).1 hr.le, fun i => (div_le_one hr).mpr (hv i).2⟩
  have hv' : ((fun i => (k i : ℝ)) + r • y) = v := by
    ext i
    change (k i : ℝ) + r * ((v i - (k i : ℝ)) / r) = v i
    field_simp
    ring
  let f (p : a.support × unitBox d) := X ((fun i => ((p.1 : Freq d) i : ℝ)) + r • (p.2 : Space d))
  have hf : Continuous f := (continuous_packet_cost a hX).comp (.prodMk_right r)
  apply le_csSup (isCompact_univ.bddAbove_image hf.continuousOn)
  exact ⟨(⟨k,hk⟩,⟨y,hy⟩), mem_univ _, congrArg X hv'⟩

theorem mtEnvelope_zero_attained (a : Freq d →₀ ℂ) {X : Space d → ℝ} (hX : Continuous X)
    (ha : a.support.Nonempty) :
    ∃ k ∈ a.support, mtEnvelope a X 0 = X (fun i => (k i : ℝ)) := by
  let : CompactSpace (unitBox d) := isCompact_iff_compactSpace.mp isCompact_Icc
  let f (p : a.support × unitBox d) := X ((fun i => ((p.1 : Freq d) i : ℝ)) + (0 : ℝ) • (p.2 : Space d))
  have hf : Continuous f := (continuous_packet_cost a hX).comp (.prodMk_right 0)
  have hne : (univ : Set (a.support × unitBox d)).Nonempty :=
    ⟨(Classical.choice ha.to_subtype, ⟨0, ⟨le_rfl, fun _ => zero_le_one⟩⟩), mem_univ _⟩
  obtain ⟨p, _, hp, _⟩ := isCompact_univ.exists_sSup_image_eq_and_ge hne hf.continuousOn
  exact ⟨p.1,p.1.property, by simpa [mtEnvelope, f] using hp⟩

end RTS.Transference
