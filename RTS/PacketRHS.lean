module

public import RTS.PacketData
public import RTS.LiftedRays
public import RTS.BoxAverages

/-! Exactly normalized frequency-side quantities for thickened lattice data. -/
@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace RTS.Transference

variable {d : ℕ}

theorem rayMax_nonneg {w : Torus d × UnitAddCircle → ℝ} (h₀ : ∀ z, 0 ≤ w z)
    (v : Space d) : 0 ≤ continuousRayMax (realTimeWeight w) v := by
  apply Real.sSup_nonneg
  rintro _ ⟨x,_,rfl⟩
  exact integral_nonneg fun _ => h₀ _

theorem profile_mass {r : ℝ} (hr : r < 1/2) (a : Freq d →₀ ℂ) :
    (∫⁻ ξ, ‖thickenedProfile (packetBump d r) a ξ‖ₑ^2) =
      ENNReal.ofReal r ^ d * (∑ k ∈ a.support, ‖a k‖ₑ^2) := by
  have h := profile_integral hr a (fun _ => 1) measurable_const
  simpa only [mul_one, lintegral_one, Measure.restrict_apply_univ, volume_originBox,
    ← Finset.sum_mul, mul_comm (∑ k ∈ a.support, ‖a k‖ₑ^2)] using h

theorem real_profile_integral {r : ℝ} (hr : 0 < r) (hr' : r < 1/2)
    (a : Freq d →₀ ℂ) (H : Space d → ℝ) (hH : Continuous H) (h₀ : ∀ v, 0 ≤ H v) :
    (∫⁻ ξ, ‖thickenedProfile (packetBump d r) a ξ‖ₑ^2 * ENNReal.ofReal (H ξ)) =
      ENNReal.ofReal (r^d * steinAverage a H r) := by
  rw [profile_integral hr' a (fun ξ => ENNReal.ofReal (H ξ)) (ENNReal.continuous_ofReal.comp hH).measurable]
  have hterm (k : Freq d) : (∫⁻ η in originBox d r, ENNReal.ofReal (H (latticePoint k + η))) =
      ENNReal.ofReal (r^d * boxAverage r (fun η => H (latticePoint k + η))) := by
    have hc : Continuous (fun η => H (latticePoint k + η)) :=
      hH.comp (continuous_const.add continuous_id)
    have hi : IntegrableOn (fun η => H (latticePoint k + η)) (originBox d r) := by
      apply (hc.integrableOn_Icc (a := (0 : Space d)) (b := fun _ => r)).mono_set
      intro η hη
      exact ⟨fun i => (mem_originBox.mp hη i).1.le, fun i => (mem_originBox.mp hη i).2⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => h₀ _),
      integral_originBox r hr]
  simp_rw [hterm]
  unfold steinAverage
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
    (fun k _ => mul_nonneg (pow_nonneg hr.le _) (mul_nonneg (sq_nonneg _)
      (boxAverage_nonneg (fun η => h₀ _) _)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem stein_profile_rhs {r : ℝ} (hr : 0 < r) (hr' : r < 1/2) (a : Freq d →₀ ℂ)
    (w : Torus d × UnitAddCircle → ℝ) (hw : Continuous w) (h₀ : ∀ z, 0 ≤ w z) :
    eucRHS .stein (thickenedProfile (packetBump d r) a) (liftedWeight w) =
      ENNReal.ofReal (r^d * steinAverage a (continuousRayMax (realTimeWeight w)) r) := by
  simp only [eucRHS, lifted_eucXray_sup w hw h₀]
  exact real_profile_integral hr hr' a _ (continuous_rayMax (realTimeWeight_continuous hw))
    (rayMax_nonneg h₀)

end RTS.Transference
