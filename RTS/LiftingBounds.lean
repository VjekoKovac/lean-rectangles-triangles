module

public import RTS.Combinatorics

/-! Common scale and uniform fixed-modulus bounds for §2.3. -/
@[expose] public noncomputable section
namespace RTS
open Real

def liftScale (t : ℕ) : ℝ := (t : ℝ)^4 * log t

/-- The two absolute-error estimates after absorbing the error at the fixed
modulus. The coefficient b may depend on the modulus but is common to both
bounds, so it disappears from every ratio. -/
def UniformLiftBounds (A : ℕ → Finset Point) (C target : ℝ) (q : ℕ) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∀ t : ℕ, exp (C * (q : ℝ)^2) ≤ t →
    target * b * liftScale t ≤ rectangleCount (A t) ∧
    ((A t).card * maxPinnedCount (A t) : ℕ) ≤ b * liftScale t

end RTS
