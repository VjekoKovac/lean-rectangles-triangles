module

public import RTS.PacketIdentities
public import RTS.PacketBox
public import RTS.SpatialTiling
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The period-cell identities for the weighted left side -/

@[expose] public noncomputable section
namespace RTS.Transference
open Set MeasureTheory Filter
open scoped ENNReal Topology
variable {d : ℕ}

def weighOnCell (w : Torus d × UnitAddCircle → ℝ) (p : Space d × ℝ) : ℝ :=
  w (fun i => (p.1 i : UnitAddCircle), (p.2 : UnitAddCircle))

theorem continuous_weighOnCell {w : Torus d × UnitAddCircle → ℝ} (hw : Continuous w) :
    Continuous (weighOnCell w) := by
  apply hw.comp
  exact (continuous_pi fun i => (AddCircle.continuous_mk' (1:ℝ)).comp ((continuous_apply i).comp continuous_fst)).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd)

private theorem translated_weight (w : Torus d × UnitAddCircle → ℝ)
    (x : Space d) (j : Freq d) (t : ℝ) :
    weighOnCell w (x+latticePoint j,t) = weighOnCell w (x,t) := by
  have he (i : Fin d) : (((j i : ℤ):ℝ) : UnitAddCircle) = 0 := by
    have h := AddCircle.coe_period (p := (1:ℝ))
    calc
      _ = (↑((j i) • (1 : ℝ)) : UnitAddCircle) := by simp
      _ = _ := by rw [AddCircle.coe_zsmul, h, smul_zero]
  simp only [weighOnCell, latticePoint, Pi.add_apply, QuotientAddGroup.mk_add, he, add_zero]

private theorem measurable_euc_space {F : Space d → ℂ} (hF : Measurable F) (t : ℝ) :
    Measurable (fun x => eucWave F x t) := by
  have hp : Continuous (fun z : Space d × Space d => euPhase z.1 z.2 t) := by
    unfold euPhase dot
    fun_prop
  have h : StronglyMeasurable (fun z : Space d × Space d => F z.2 * euPhase z.1 z.2 t) :=
    ((hF.comp measurable_snd).mul hp.measurable).stronglyMeasurable
  exact h.integral_prod_right'.measurable

private theorem closedCube_ae : periodCube d =ᵐ[volume] Icc (0 : Space d) (fun _ => 1) :=
by
  have h := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ)) (f := (0 : Space d)) (g := fun _ => (1:ℝ))
  have he : periodCube d = Set.univ.pi (fun _ : Fin d => Ioc (0:ℝ) 1) := by
    ext x
    simp [periodCube]
  rw [he]
  exact h

/-- A continuous nonnegative spacetime density has its lower integral equal
to the ordinary iterated integral on the closed unit cell. -/
theorem cell_ofReal_integral (b : Space d × ℝ → ℝ) (hb : Continuous b) (hp : ∀ z, 0 ≤ b z) :
    (∫⁻ t in Icc (0:ℝ) 1, ∫⁻ x in Icc (0:Space d) (fun _ => 1), ENNReal.ofReal (b (x,t))) =
      ENNReal.ofReal (∫ t in Icc (0:ℝ) 1, ∫ x in Icc (0:Space d) (fun _ => 1), b (x,t)) := by
  have hh : Continuous (fun t : ℝ => ∫ x in Icc (0:Space d) (fun _ => 1), b (x,t)) := by
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact hb.comp continuous_swap
  rw [ofReal_integral_eq_lintegral_ofReal (hh.continuousOn.integrableOn_compact isCompact_Icc)
    (ae_of_all _ fun t => integral_nonneg (fun x => hp (x,t)))]
  apply lintegral_congr
  intro t
  exact (ofReal_integral_eq_lintegral_ofReal
    ((hb.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact isCompact_Icc)
    (ae_of_all _ fun x => hp (x,t))).symm

/-- Lifting a nonnegative continuous weight and summing over translations
produces the packet energy density on the unit cell. -/
theorem lift_cell_identity (F : Space d → ℂ) (hm : Measurable F)
    (w : Torus d × UnitAddCircle → ℝ) (hw : Continuous w) (hw₀ : ∀ z, 0 ≤ w z)
    (b : Space d × ℝ → ℝ) (hb : Continuous b) (hs : ∀ (x : Space d) (t : ℝ),
      HasSum (fun j : Freq d => ‖eucWave F (x+latticePoint j) t‖^2) (b (x,t))) :
    eucLHS F (liftedWeight w) = ENNReal.ofReal
      (∫ t in Icc (0:ℝ) 1, ∫ x in Icc (0:Space d) (fun _ => 1), b (x,t) * weighOnCell w (x,t)) := by
  have h0 (x : Space d) (t : ℝ) : 0 ≤ b (x,t) := (hs x t).nonneg (fun _ => sq_nonneg _)
  rw [← cell_ofReal_integral (fun p => b p * weighOnCell w p)
    (hb.mul (continuous_weighOnCell hw)) (fun p => mul_nonneg (h0 _ _) (hw₀ _))]
  unfold eucLHS
  apply setLIntegral_congr_fun_ae measurableSet_Icc
  filter_upwards [(show ∀ᵐ t : ℝ, (t ∈ Ioc 0 1 ↔ t ∈ Icc 0 1) from eventuallyEqSet_iff.mp Ioc_ae_eq_Icc)] with t ht
  intro ht'
  have ht0 := ht.mpr ht'
  let f (x : Space d) := ‖eucWave F x t‖ₑ ^ 2 * ENNReal.ofReal (weighOnCell w (x,t))
  have hf : Measurable f := ((measurable_euc_space hm t).enorm.pow_const _).mul
    (ENNReal.continuous_ofReal.comp ((continuous_weighOnCell hw).comp (continuous_id.prodMk continuous_const))).measurable
  have he : (∫⁻ x, ‖eucWave F x t‖ₑ ^ 2 * ENNReal.ofReal (liftedWeight w (x,t))) = ∫⁻ x, f x := by
    simp only [liftedWeight, ite_eq_left ht0, f, weighOnCell]
  rw [he, lintegral_periodize f hf, setLIntegral_congr closedCube_ae]
  apply lintegral_congr
  intro x
  change (∑' j : Freq d, ‖eucWave F (x+latticePoint j) t‖ₑ ^ 2 * ENNReal.ofReal
    (weighOnCell w (x+latticePoint j,t))) = _
  simp only [translated_weight, ENNReal.tsum_mul_right, ENNReal.ofReal_mul (h0 x t)]
  congr 1
  rw [← (hs x t).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hs x t).summable]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]


private theorem periodic_cube_integral (f : Torus d → ℝ≥0∞) :
    (∫⁻ x, f x ∂torusMeasure d) = ∫⁻ x in Icc (0:Space d) (fun _ => 1),
      f (fun i => (x i : UnitAddCircle)) := by
  have he : (∫⁻ x, f x ∂torusMeasure d) = ∫⁻ x : Space d in {x : Space d | ∀ i, x i ∈ Ioc ((0:Space d) i) ((0:Space d) i+1)}, f (fun i => (x i : UnitAddCircle)) := UnitAddTorus.lintegral_preimage f (0:Space d)
  calc
    _ = ∫⁻ x in periodCube d, f (fun i => (x i : UnitAddCircle)) := by
      simpa [periodCube] using he
    _ = _ := setLIntegral_congr closedCube_ae

/-- The zero-shift limit of the cell density gives exactly the periodic left side. -/
theorem perLHS_cell (a : Freq d →₀ ℂ) (w : Torus d × UnitAddCircle → ℝ)
    (hw : Continuous w) (hw₀ : ∀ z, 0 ≤ w z) :
    perLHS a w = ENNReal.ofReal (∫ t in Icc (0:ℝ) 1, ∫ x in Icc (0:Space d) (fun _ => 1),
      ‖shiftedWave a (x,t) 0‖^2 * weighOnCell w (x,t)) := by
  have hb : Continuous (fun p : Space d × ℝ => ‖shiftedWave a p 0‖^2 * weighOnCell w p) :=
    (((shiftedWave_continuous a).comp (continuous_id.prodMk continuous_const)).norm.pow 2).mul
      (continuous_weighOnCell hw)
  rw [← cell_ofReal_integral _ hb (fun _ => mul_nonneg (sq_nonneg _) (hw₀ _))]
  let f (t : UnitAddCircle) := ∫⁻ x, ‖perWave a x t‖ₑ ^ 2 * ENNReal.ofReal (w (x,t)) ∂torusMeasure d
  change (∫⁻ t, f t ∂circleMeasure) = _
  have hc : (volume : Measure UnitAddCircle) = circleMeasure := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp [circleMeasure]
  rw [← hc, ← UnitAddCircle.lintegral_preimage 0 f, zero_add, setLIntegral_congr Ioc_ae_eq_Icc]
  apply lintegral_congr
  intro t
  dsimp [f]
  rw [periodic_cube_integral]
  apply lintegral_congr
  intro x
  simp only [shiftedWave_zero, weighOnCell, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Exact finite-radius identity for the box packet used in the transference proof. -/
theorem packetLHS_cell (a : Freq d →₀ ℂ) (w : Torus d × UnitAddCircle → ℝ) (hw : Continuous w)
    (hw₀ : ∀ z, 0 ≤ w z) (r : ℝ) (hr : r ≤ 1) :
    eucLHS (thickenedProfile (packetBump d r) a) (liftedWeight w) =
      ENNReal.ofReal (∫ t in Icc (0:ℝ) 1, ∫ x in Icc (0:Space d) (fun _ => 1),
        (∫ η in originBox d r, ‖shiftedWave a (x,t) η‖^2) * weighOnCell w (x,t)) := by
  let b (p : Space d × ℝ) := ∫ η in originBox d r, ‖shiftedWave a p η‖^2
  have hbox : originBox d r =ᵐ[volume] Icc (0:Space d) (fun _ => r) :=
    Measure.univ_pi_Ioc_ae_eq_Icc
  have hb : Continuous b := by
    unfold b
    simp_rw [setIntegral_congr_set hbox]
    exact continuous_parametric_integral_of_continuous ((shiftedWave_continuous a).norm.pow 2)
      isCompact_Icc
  have hm : Measurable (thickenedProfile (packetBump d r) a) := by
    unfold thickenedProfile
    apply Finset.measurable_sum
    intro k hk
    exact measurable_const.mul ((measurable_packetBump d r).comp (measurable_id.sub measurable_const))
  apply lift_cell_identity _ hm w hw hw₀ b hb
  intro x t
  have hs : originBox d r ⊆ frequencyCell (0:Space d) := by
    intro η hη i
    simpa using (show η i ∈ Ioc 0 1 from ⟨(mem_originBox.mp hη i).1, (mem_originBox.mp hη i).2.trans hr⟩)
  have hsupport : Function.support (packetBump d r) ⊆ frequencyCell (0:Space d) := by
    intro y hy
    apply hs
    by_contra hh
    exact hy (by simp [packetBump,hh])
  have h := physical_packet_hasSum _ (packetBump_integrable d r) (measurable_packetBump d r)
    1 (packetBump_bound d r) 0 hsupport a x t
  convert h using 1
  have he : (fun η => ‖packetBump d r η‖^2 * ‖shiftedWave a (x,t) η‖^2) =
      (originBox d r).indicator (fun η => ‖shiftedWave a (x,t) η‖^2) := by
    funext η
    by_cases hη : η ∈ originBox d r <;> simp [packetBump,hη]
  rw [he, integral_indicator (measurableSet_originBox ..),
    Measure.restrict_restrict (measurableSet_originBox ..), Set.inter_eq_left.mpr hs]

end RTS.Transference
