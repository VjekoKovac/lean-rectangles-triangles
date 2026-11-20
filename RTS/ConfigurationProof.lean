module

public import RTS.ConfigurationBridge
public import RTS.ConfigurationCounts

@[expose] public section

noncomputable section
open scoped ENNReal

namespace RTS.Configuration

private theorem ofReal_sup_le {s : Set ℝ} {b : ℝ≥0∞}
    (h : ∀ t ∈ s, ENNReal.ofReal t ≤ b) : ENNReal.ofReal (sSup s) ≤ b := by
  by_cases hb : b = ⊤
  · simp [hb]
  apply ENNReal.ofReal_le_of_le_toReal
  rcases s.eq_empty_or_nonempty with he | hn
  · simp [he, Real.sSup_empty]
  exact csSup_le hn (fun t ht => (ENNReal.ofReal_le_iff_le_toReal hb).mp (h t ht))

/-- Theorem 1.4. Each admissible constant must work for the indicator of every
eligible frequency set A and its specific weight |u_A|². -/
theorem configurationLowerBounds : ConfigurationLowerBounds := by
  intro N _ n _
  refine ⟨ofReal_sup_le ?_, ofReal_sup_le ?_, ofReal_sup_le ?_, ofReal_sup_le ?_⟩
  · rintro _ ⟨A, _, hb, rfl⟩
    exact ratio_le_perBest A (perInBox N)
      (by simpa only [perInBox, inBox, FitsBox, configCoeff_support] using hb)
      (rectangle_integral A) (pinned_integral_le A)
  · rintro _ ⟨A, hc, rfl⟩
    exact ratio_le_perBest A (fun a => a.support.card = n)
      (by simpa only [configCoeff_support] using hc)
      (rectangle_integral A) (pinned_integral_le A)
  · rintro _ ⟨A, _, hb, rfl⟩
    exact pinnedRatio_le_perBest A (perInBox N)
      (by simpa only [perInBox, inBox, FitsBox, configCoeff_support] using hb)
      (rectangle_integral A) (pinned_integral_le A)
  · rintro _ ⟨A, hc, rfl⟩
    exact pinnedRatio_le_perBest A (fun a => a.support.card = n)
      (by simpa only [configCoeff_support] using hc)
      (rectangle_integral A) (pinned_integral_le A)

end RTS.Configuration
