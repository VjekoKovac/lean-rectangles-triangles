module

public import RTS.AnalysisDefs

@[expose] public section

namespace RTS

/-- Theorem 1.5 of Bennett–Kovač–Nakamura–Oliveira. In each dimension the
constants and thresholds are uniform in the real box parameter and the natural
support size. Both upper and both lower cardinality estimates are asserted. -/
def TrigonometricGrowth : Prop := ∀ d : ℕ, 1 ≤ d →
  (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    ENNReal.ofReal (c * (Real.log N)^d) ≤ perStein d N ∧
    ENNReal.ofReal (c * (Real.log N)^d) ≤ perMT d N) ∧
  (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ENNReal.ofReal (c * n) ≤ perSteinCard d n ∧
    ENNReal.ofReal (c * n) ≤ perMTCard d n ∧
    perSteinCard d n ≤ ENNReal.ofReal (C * n) ∧
    perMTCard d n ≤ ENNReal.ofReal (C * n))

end RTS
