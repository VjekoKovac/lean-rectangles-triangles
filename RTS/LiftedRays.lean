module

public import RTS.PacketIdentities

/-! Passage from the Euclidean X-ray of a periodic weight cut off in time to the
maximum of its real-valued ray averages on the compact spatial torus. -/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace RTS.Transference

variable {d : ℕ}

private def base (x : Space d) : Torus d := fun i => (x i : UnitAddCircle)

private theorem base_surjective : Function.Surjective (base (d := d)) := by
  intro x
  choose y hy using fun i => QuotientAddGroup.mk_surjective (x i)
  exact ⟨y, funext hy⟩

/-- The time-truncated periodic weight is measurable and locally integrable. -/
theorem liftedWeight_eligible (w : Torus d × UnitAddCircle → ℝ)
    (hw : Continuous w) (h₀ : ∀ z, 0 ≤ w z) : eucWeight (liftedWeight w) := by
  refine ⟨fun z => by unfold liftedWeight; split <;> simp [h₀], ?_⟩
  let f (z : Space d × ℝ) := w (base z.1, (z.2 : UnitAddCircle))
  have hf : Continuous f := by
    apply hw.comp
    apply Continuous.prodMk
    · apply continuous_pi; intro i
      exact (AddCircle.continuous_mk' 1).comp ((continuous_apply i).comp continuous_fst)
    · exact (AddCircle.continuous_mk' 1).comp continuous_snd
  let E : Set (Space d × ℝ) := Prod.snd ⁻¹' Ioc 0 1
  have hE : MeasurableSet E := measurable_snd measurableSet_Ioc
  have eq : liftedWeight w = E.indicator f := by
    funext z
    by_cases hz : z.2 ∈ Ioc (0:ℝ) 1 <;> simp [liftedWeight, E, f, hz] <;> rfl
  rw [eq]
  exact (hf.locallyIntegrable (μ := volume)).indicator hE

/-- The untruncated integrand on one time period. -/
abbrev realTimeWeight (w : Torus d × UnitAddCircle → ℝ) (z : Torus d × ℝ) : ℝ :=
  w (z.1,(z.2 : UnitAddCircle))

theorem realTimeWeight_continuous {w : Torus d × UnitAddCircle → ℝ} (hw : Continuous w) :
    Continuous (realTimeWeight w) :=
  hw.comp (continuous_fst.prodMk ((AddCircle.continuous_mk' 1).comp continuous_snd))

private def average (w : Torus d × UnitAddCircle → ℝ) (v : Space d) (x : Torus d) : ℝ :=
  ∫ t in Icc (0:ℝ) 1, w (fun i => x i - (↑(2*t*v i) : UnitAddCircle), (t : UnitAddCircle))

private theorem average_continuous {w : Torus d × UnitAddCircle → ℝ}
    (hw : Continuous w) (v : Space d) : Continuous (average w v) := by
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  apply hw.comp
  apply Continuous.prodMk
  · apply continuous_pi; intro i
    apply Continuous.sub ((continuous_apply i).comp continuous_fst)
    apply (AddCircle.continuous_mk' 1).comp
    fun_prop
  · exact (AddCircle.continuous_mk' 1).comp continuous_snd

private theorem xray_lift_ofReal (w : Torus d × UnitAddCircle → ℝ)
    (hw : Continuous w) (h₀ : ∀ z, 0 ≤ w z) (x v : Space d) :
    eucXray (liftedWeight w) x v = ENNReal.ofReal (average w v (base x)) := by
  let g (t : ℝ) := w ((fun i => base x i - (↑(2*t*v i) : UnitAddCircle)), (t : UnitAddCircle))
  have hg : Continuous g := by
    apply hw.comp
    apply Continuous.prodMk
    · apply continuous_pi; intro i
      exact (continuous_const (y := base x i)).sub ((AddCircle.continuous_mk' 1).comp
        (by fun_prop : Continuous (fun t : ℝ => 2*t*v i)))
    · exact AddCircle.continuous_mk' 1
  have hi (t : ℝ) : ENNReal.ofReal (liftedWeight w (fun i => x i - 2*t*v i,t)) =
      (Ioc (0:ℝ) 1).indicator (fun t => ENNReal.ofReal (g t)) t := by
    by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [liftedWeight, ht, g, base, QuotientAddGroup.mk_sub]
  unfold eucXray
  simp_rw [hi]
  rw [lintegral_indicator measurableSet_Ioc, restrict_Ioc_eq_restrict_Icc]
  exact (ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_Icc)
    (Filter.Eventually.of_forall fun t => h₀ _)).symm

/-- Supremum over real base points equals the compact-torus maximum of ray averages. -/
theorem lifted_eucXray_sup (w : Torus d × UnitAddCircle → ℝ)
    (hw : Continuous w) (h₀ : ∀ z, 0 ≤ w z) (v : Space d) :
    (⨆ x, eucXray (liftedWeight w) x v) =
      ENNReal.ofReal (continuousRayMax (realTimeWeight w) v) := by
  change _ = ENNReal.ofReal (sSup (average w v '' univ))
  obtain ⟨a, _, ha, hmax⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    (s := (univ : Set (Torus d))) univ_nonempty (average_continuous hw v).continuousOn
  obtain ⟨x,hx⟩ := base_surjective a
  rw [ha]
  apply le_antisymm
  · refine iSup_le fun y => ?_
    rw [xray_lift_ofReal w hw h₀]
    exact ENNReal.ofReal_le_ofReal (hmax _ (mem_univ _))
  · apply le_iSup_of_le x
    rw [xray_lift_ofReal w hw h₀, hx]

/-- The specialization at lattice velocities agrees with the periodic geodesic ray. -/
theorem perXray_sup_eq_continuousRayMax (w : Torus d × UnitAddCircle → ℝ)
    (hw : Continuous w) (h₀ : ∀ z, 0 ≤ w z) (k : Freq d) :
    (⨆ x, perXray w x k) = ENNReal.ofReal (continuousRayMax (realTimeWeight w) (latticePoint k)) := by
  rw [← lifted_eucXray_sup w hw h₀]
  simp_rw [show ∀ x, eucXray (liftedWeight w) x (latticePoint k) = perXray w (base x) k
    from fun x => integer_ray_lift w x k]
  exact (Function.Surjective.iSup_comp base_surjective _).symm

end RTS.Transference
