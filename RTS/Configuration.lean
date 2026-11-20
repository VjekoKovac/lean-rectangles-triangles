module

public import RTS.AnalysisDefs
public import RTS.Combinatorics

@[expose] public section

namespace RTS

/-- The four lower bounds of Theorem 1.4. The radius is real and the support size is exact. -/
def ConfigurationLowerBounds : Prop :=
  ∀ N : ℝ, 1 ≤ N → ∀ n : ℕ, 0 < n →
    ENNReal.ofReal (boxRatio N) ≤ perStein 2 N ∧
    ENNReal.ofReal (sizeRatio n) ≤ perSteinCard 2 n ∧
    ENNReal.ofReal (pinnedBoxRatio N) ≤ perMT 2 N ∧
    ENNReal.ofReal (pinnedSizeRatio n) ≤ perMTCard 2 n

namespace Configuration

open MeasureTheory
open scoped BigOperators

/-- The periodized Schrödinger sum for coefficient one at each point of A. -/
noncomputable def configWave (A : Finset Point) (x : Torus 2) (t : UnitAddCircle) : ℂ :=
  ∑ k ∈ A, UnitAddTorus.mFourier k x * fourier (∑ i, k i ^ 2) t

end Configuration
end RTS
