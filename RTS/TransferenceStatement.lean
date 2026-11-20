module

public import RTS.AnalysisDefs

@[expose] public section

namespace RTS

/-- Theorem 1.3, with coefficient one and a unit enlargement of the real frequency radius. -/
def QuantitativeTransference : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ N : ℝ, 1 ≤ N →
    perStein d N ≤ eucStein d (N + 1) ∧ perMT d N ≤ eucMT d (N + 1)

end RTS
