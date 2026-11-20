module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Challenge: Rectangles, triangles and Schrödinger waves

Read this file independently of the proof modules. The four theorems at the end
are the targets from arXiv:2606.30178v1. The intentional holes specify the
challenge for Lean Comparator. No solution module may import this file.
-/

@[expose] public section

namespace RTS

open scoped BigOperators

abbrev Point := Fin 2 → ℤ

def dot₂ (x y : Point) : ℤ := ∑ i, x i * y i

def IsRectangle (a b c e : Point) : Prop :=
  a + c = b + e ∧ dot₂ (b - a) (e - a) = 0

def IsTriangle (a b k : Point) : Prop :=
  dot₂ (2 • k - a - b) (b - a) = 0

/-- The four independent choices retain all orderings and all coincidences. -/
def rectangleCount (A : Finset Point) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A,
    (A.filter fun e => a + c = b + e ∧ dot₂ (b - a) (e - a) = 0).card

/-- Counts ordered bases of triangles with the specified apex. Used at apexes in A. -/
def pinnedTriangleCount (A : Finset Point) (k : Point) : ℕ :=
  ∑ a ∈ A, (A.filter fun b => dot₂ (2 • k - a - b) (b - a) = 0).card

def triangleCount (A : Finset Point) : ℕ :=
  ∑ k ∈ A, pinnedTriangleCount A k

def maxPinnedCount (A : Finset Point) : ℕ :=
  A.sup (pinnedTriangleCount A)

noncomputable def ratio (A : Finset Point) : ℝ :=
  (rectangleCount A : ℝ) / triangleCount A

noncomputable def pinnedRatio (A : Finset Point) : ℝ :=
  (rectangleCount A : ℝ) / (A.card * maxPinnedCount A : ℕ)

/-- Each integer coordinate lies in the real interval [-N,N]. -/
def FitsBox (N : ℝ) (A : Finset Point) : Prop :=
  ∀ k ∈ A, ∀ i, |(k i : ℝ)| ≤ N

noncomputable def boxRatio (N : ℝ) : ℝ :=
  sSup {r | ∃ A : Finset Point, A.Nonempty ∧ FitsBox N A ∧ ratio A = r}

noncomputable def pinnedBoxRatio (N : ℝ) : ℝ :=
  sSup {r | ∃ A : Finset Point, A.Nonempty ∧ FitsBox N A ∧ pinnedRatio A = r}

noncomputable def sizeRatio (n : ℕ) : ℝ :=
  sSup {r | ∃ A : Finset Point, A.card = n ∧ ratio A = r}

noncomputable def pinnedSizeRatio (n : ℕ) : ℝ :=
  sSup {r | ∃ A : Finset Point, A.card = n ∧ pinnedRatio A = r}

/-- The exponent is c divided by the third iterated natural logarithm. -/
noncomputable def logGrowth (c x : ℝ) : ℝ :=
  (Real.log x) ^ (c / Real.log (Real.log (Real.log x)))

end RTS

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

namespace RTS

/-- Theorem 1.2. The same positive constant works for the two eventual estimates. -/
def CombinatorialGrowth : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      pinnedBoxRatio N ≤ boxRatio N ∧ logGrowth c N ≤ pinnedBoxRatio N) ∧
    (∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      pinnedSizeRatio n ≤ sizeRatio n ∧ logGrowth c n ≤ pinnedSizeRatio n)

/-- Theorem 1.3, with coefficient one and a unit enlargement of the real frequency radius. -/
def QuantitativeTransference : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ N : ℝ, 1 ≤ N →
    perStein d N ≤ eucStein d (N + 1) ∧ perMT d N ≤ eucMT d (N + 1)

/-- The four lower bounds of Theorem 1.4. The radius is real and the support size is exact. -/
def ConfigurationLowerBounds : Prop :=
  ∀ N : ℝ, 1 ≤ N → ∀ n : ℕ, 0 < n →
    ENNReal.ofReal (boxRatio N) ≤ perStein 2 N ∧
    ENNReal.ofReal (sizeRatio n) ≤ perSteinCard 2 n ∧
    ENNReal.ofReal (pinnedBoxRatio N) ≤ perMT 2 N ∧
    ENNReal.ofReal (pinnedSizeRatio n) ≤ perMTCard 2 n

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

/-- Paper, Theorem 1.2. -/
theorem combinatorial_growth : CombinatorialGrowth := by sorry

/-- Paper, Theorem 1.3. -/
theorem quantitative_transference : QuantitativeTransference := by sorry

/-- Paper, Theorem 1.4. -/
theorem configuration_lower_bounds : ConfigurationLowerBounds := by sorry

/-- Paper, Theorem 1.5. -/
theorem trigonometric_growth : TrigonometricGrowth := by sorry

end RTS
