module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Ordered configurations from §1.1 of Bennett–Kovač–Nakamura–Oliveira. -/

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

/-- Theorem 1.2. The same positive constant works for the two eventual estimates. -/
def CombinatorialGrowth : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      pinnedBoxRatio N ≤ boxRatio N ∧ logGrowth c N ≤ pinnedBoxRatio N) ∧
    (∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      pinnedSizeRatio n ≤ sizeRatio n ∧ logGrowth c n ≤ pinnedSizeRatio n)

end RTS
