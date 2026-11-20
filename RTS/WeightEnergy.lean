module

public import RTS.WeightTest
public import RTS.WeightCollisions
public import Mathlib.MeasureTheory.Integral.Prod

/-! Parseval identifies the numerator of the dyadic test with the collision count
of the paper's product polynomial. -/
@[expose] public section

noncomputable section
namespace RTS.Dyadic

open MeasureTheory Configuration
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem wave_mul_auxPoly (m r : Fin d → ℕ) (x : Torus d) (t : UnitAddCircle) :
    perWave (data m) x t * auxPoly m r x t =
      ∑ p ∈ testTerms m r, atom (productSpace m p) (productTime m p) x t := by
  simp only [perWave_data, auxPoly, testTerms, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J _ =>
    atom_mul (frequency m j) (spaceFreq m J) _ _ _ _

theorem dyadicLHScollisions (m r : Fin d → ℕ) :
    perLHS (data m) (weight m r) = (collisions m r).card := by
  classical
  let F (z : UnitAddCircle × Torus d) : ℝ :=
    ‖∑ p ∈ testTerms m r, atom (productSpace m p) (productTime m p) z.2 z.1‖^2
  have hF : Continuous F := by unfold F atom; fun_prop
  have hI : Integrable F (circleMeasure.prod (torusMeasure d)) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : 0 ≤ᵐ[circleMeasure.prod (torusMeasure d)] F :=
    Filter.Eventually.of_forall fun z => sq_nonneg _
  have he := atom_energy (testTerms m r) (productSpace m) (productTime m)
  simp_rw [integral_complex_ofReal] at he
  have h := congrArg Complex.re he
  simp only [Complex.ofReal_re, Complex.natCast_re] at h
  change (∫ t, ∫ x, F (t,x) ∂torusMeasure d ∂circleMeasure) = ((collisions m r).card : ℝ) at h
  rw [← ENNReal.ofReal_natCast, ← h, ← integral_prod F hI,
    ofReal_integral_eq_lintegral_ofReal hI h0, lintegral_prod (fun z => ENNReal.ofReal (F z))
      (ENNReal.continuous_ofReal.comp hF).aemeasurable]
  unfold perLHS
  apply lintegral_congr
  intro t
  apply lintegral_congr
  intro x
  change ‖perWave (data m) x t‖ₑ ^ 2 * ENNReal.ofReal (‖auxPoly m r x t‖ ^ 2) = _
  dsimp only [F]
  rw [← wave_mul_auxPoly, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end RTS.Dyadic
