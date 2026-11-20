module

public import RTS.ContinuousTransference
public import RTS.WeightReduction
public import RTS.TransferenceStatement

/-! # Theorem 1.3 of Bennett–Kovač–Nakamura–Oliveira -/

@[expose] public section
open scoped ENNReal

namespace RTS

private theorem periodic_le_euclidean {d : ℕ} (N : ℝ) (kind : EstimateKind) :
    perBest (d := d) kind (perInBox N) ≤ eucBest d kind (N+1) := by
  apply le_sInf
  intro C hE
  by_cases hC : C = ∞
  · exact hC ▸ le_top
  apply sInf_le
  apply Smoothing.perAdmissible_of_continuous
  intro a ha w hw hcont
  exact Transference.continuous_transfer kind hC hE a ha w hcont hw.1

/-- A radius `N` periodic estimate is bounded by the Euclidean estimate at radius
`N+1`, with no loss in the multiplicative constant, for both weighted estimates. -/
theorem quantitativeTransference : QuantitativeTransference := by
  intro d _ N _
  exact ⟨periodic_le_euclidean N .stein, periodic_le_euclidean N .mt⟩

end RTS
