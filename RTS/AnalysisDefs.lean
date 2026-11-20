module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The sharp weighted Schrödinger constants

Data are specified by their Fourier coefficients. Periodic coefficients are finitely
supported. In Euclidean space we use arbitrary square-integrable frequency profiles
whose essential closed supports lie in the prescribed box. The support is the support
of the measure with density `‖F‖²`, so changing values on a null set has no effect.

We retain actual representatives of weights, since the X-ray expressions restrict them
to individual lines. Nonnegative integrals, suprema, and infima take values in ℝ≥0∞.
The measures of each period circle and each spatial torus are one.
-/

@[expose] public section

namespace RTS

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

abbrev Freq (d : ℕ) := Fin d → ℤ
abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)

abbrev circleMeasure : Measure UnitAddCircle := AddCircle.haarAddCircle
abbrev torusMeasure (d : ℕ) : Measure (Torus d) :=
  Measure.pi (fun _ : Fin d => circleMeasure)

def dot {d : ℕ} (x y : Space d) : ℝ := ∑ i, x i * y i

def inBox {d : ℕ} (N : ℝ) (ξ : Space d) : Prop := ∀ i, |ξ i| ≤ N

def perInBox {d : ℕ} (N : ℝ) (a : Freq d →₀ ℂ) : Prop :=
  ∀ k ∈ a.support, inBox N (fun i => (k i : ℝ))

/-- `e^{2πi(x·ξ + t|ξ|²)}` with the sign convention of the source. -/
def euPhase {d : ℕ} (x ξ : Space d) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (dot x ξ + t * dot ξ ξ)) : ℝ) * Complex.I)

def eucWave {d : ℕ} (F : Space d → ℂ) (x : Space d) (t : ℝ) : ℂ :=
  ∫ ξ, F ξ * euPhase x ξ t

def perWave {d : ℕ} (a : Freq d →₀ ℂ) (x : Torus d) (t : UnitAddCircle) : ℂ :=
  ∑ k ∈ a.support, a k * UnitAddTorus.mFourier k x * fourier (∑ i, k i ^ 2) t

/-- The essential closed Fourier support of the datum with frequency profile `F`. -/
def freqSupport {d : ℕ} (F : Space d → ℂ) : Set (Space d) :=
  ((volume : Measure (Space d)).withDensity (fun ξ => ‖F ξ‖ₑ ^ 2)).support

def eucWeight {d : ℕ} (w : Space d × ℝ → ℝ) : Prop :=
  (∀ z, 0 ≤ w z) ∧ LocallyIntegrable w volume

def perWeight {d : ℕ} (w : Torus d × UnitAddCircle → ℝ) : Prop :=
  (∀ z, 0 ≤ w z) ∧ Integrable w ((torusMeasure d).prod circleMeasure)

/-- Integration over all real times, even though the left side only sees [0,1]. -/
def eucXray {d : ℕ} (w : Space d × ℝ → ℝ) (x v : Space d) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ENNReal.ofReal (w (fun i => x i - 2 * t * v i, t))

/-- Normalized time integral on the period circle, with velocity `2k`. -/
def perXray {d : ℕ} (w : Torus d × UnitAddCircle → ℝ)
    (x : Torus d) (k : Freq d) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (w (fun i => x i - (2 * k i) • t, t)) ∂circleMeasure

def eucLHS {d : ℕ} (F : Space d → ℂ) (w : Space d × ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1, ∫⁻ x, ‖eucWave F x t‖ₑ ^ 2 * ENNReal.ofReal (w (x,t))

def perLHS {d : ℕ} (a : Freq d →₀ ℂ) (w : Torus d × UnitAddCircle → ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ∫⁻ x, ‖perWave a x t‖ₑ ^ 2 * ENNReal.ofReal (w (x,t)) ∂torusMeasure d
    ∂circleMeasure

inductive EstimateKind where
  | stein
  | mt
  deriving DecidableEq

def perRHS {d : ℕ} (kind : EstimateKind) (a : Freq d →₀ ℂ)
    (w : Torus d × UnitAddCircle → ℝ) : ℝ≥0∞ :=
  match kind with
  | .stein => ∑ k ∈ a.support, ‖a k‖ₑ ^ 2 * ⨆ x, perXray w x k
  | .mt => (∑ k ∈ a.support, ‖a k‖ₑ ^ 2) *
      ⨆ k : ↥a.support, ⨆ x, perXray w x k

def eucRHS {d : ℕ} (kind : EstimateKind) (F : Space d → ℂ)
    (w : Space d × ℝ → ℝ) : ℝ≥0∞ :=
  match kind with
  | .stein => ∫⁻ v, ‖F v‖ₑ ^ 2 * ⨆ x, eucXray w x v
  | .mt => (∫⁻ v, ‖F v‖ₑ ^ 2) * ⨆ v : freqSupport F, ⨆ x, eucXray w x v

def perAdmissible {d : ℕ} (kind : EstimateKind) (eligible : (Freq d →₀ ℂ) → Prop)
    (C : ℝ≥0∞) : Prop :=
  ∀ a, eligible a → ∀ w, perWeight w → perLHS a w ≤ C * perRHS kind a w

def eucAdmissible {d : ℕ} (kind : EstimateKind) (N : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ F : Space d → ℂ, MemLp F 2 volume → (∀ v ∈ freqSupport F, inBox N v) →
    ∀ w, eucWeight w → eucLHS F w ≤ C * eucRHS kind F w

def perBest {d : ℕ} (kind : EstimateKind) (eligible : (Freq d →₀ ℂ) → Prop) : ℝ≥0∞ :=
  sInf {C | perAdmissible kind eligible C}

def eucBest (d : ℕ) (kind : EstimateKind) (N : ℝ) : ℝ≥0∞ :=
  sInf {C | eucAdmissible (d := d) kind N C}

def perStein (d : ℕ) (N : ℝ) : ℝ≥0∞ := perBest (d := d) .stein (perInBox N)
def perMT (d : ℕ) (N : ℝ) : ℝ≥0∞ := perBest (d := d) .mt (perInBox N)
def eucStein (d : ℕ) (N : ℝ) : ℝ≥0∞ := eucBest d .stein N
def eucMT (d : ℕ) (N : ℝ) : ℝ≥0∞ := eucBest d .mt N

def perSteinCard (d n : ℕ) : ℝ≥0∞ :=
  perBest (d := d) .stein (fun a => a.support.card = n)
def perMTCard (d n : ℕ) : ℝ≥0∞ :=
  perBest (d := d) .mt (fun a => a.support.card = n)

end
end RTS
