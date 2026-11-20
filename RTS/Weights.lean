module

public import RTS.WeightScales
public import RTS.WeightMultiplicity
public import RTS.WeightEnergy
public import RTS.WeightRays

/-! # The dyadic obstruction (Theorem 1.5) -/

@[expose] public section
namespace RTS.Dyadic

open scoped ENNReal

theorem dyadicNumerator_le {d : ℕ} (m r : Fin d → ℕ) :
    ((∏ l, (r l+1)^2 * (m l).choose (r l+1) : ℕ) : ℝ≥0∞) ≤ perLHS (data m) (weight m r) := by
  rw [dyadicLHScollisions]
  exact_mod_cast collision_count_lower m r

/-- Both tests at every dimension, all large real box radii, and both bounds
at every positive support size. -/
theorem trigonometricGrowth : TrigonometricGrowth := by
  apply trigonometricGrowth_of_dyadic
  intro d m hm eligible hel
  exact test_to_lower m hm eligible hel (fun l => m l/2) (fun _ => rfl)
    (dyadicNumerator_le ..) (dyadicMTDenom_le ..)

end RTS.Dyadic
