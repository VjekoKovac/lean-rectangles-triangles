module

public import RTS.Combinatorics
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination

/-! Quantitative residue counts and primitive-direction sieving for Lemma 2.4.
The modulus is any positive integer. No squarefreeness is needed at this stage. -/

@[expose] public noncomputable section

namespace RTS.Lifting
open Finset
open scoped BigOperators

/-- Quotients that put the progression a+qj in the real closed interval [-T,T]. -/
def indexes (q : ℕ) (a : ℤ) (T : ℝ) : Finset ℤ :=
  Icc ⌈(-T-a)/q⌉ ⌊(T-a)/q⌋

def line (q : ℕ) (a : ℤ) (T : ℝ) : Finset ℤ :=
  (indexes q a T).image (fun j => a + q*j)

theorem mem_line {q : ℕ} (hq : 0 < q) (a n : ℤ) (T : ℝ) :
    n ∈ line q a T ↔ |(n : ℝ)| ≤ T ∧ (q : ℤ) ∣ n - a := by
  have hp : (0:ℝ) < q := by exact_mod_cast hq
  simp only [line, indexes, mem_image, mem_Icc, Int.ceil_le, Int.le_floor, abs_le]
  constructor
  · rintro ⟨j, ⟨hl,hu⟩,rfl⟩
    rw [div_le_iff₀ hp] at hl
    rw [le_div_iff₀ hp] at hu
    push_cast
    refine ⟨⟨by linarith, by linarith⟩,j,by ring⟩
  · rintro ⟨⟨hl,hu⟩,j,hj⟩
    have hn : n = a + q*j := by linarith only [hj]
    subst n
    push_cast at hl hu
    exact ⟨j, ⟨(div_le_iff₀ hp).2 (by linarith), (le_div_iff₀ hp).2 (by linarith)⟩,rfl⟩

theorem line_card (q : ℕ) (hq : 0 < q) (a : ℤ) (T : ℝ) :
    (line q a T).card = (indexes q a T).card := by
  apply Finset.card_image_of_injective
  intro j l h
  exact (mul_right_inj' (by exact_mod_cast hq.ne' : (q:ℤ) ≠ 0)).mp (add_left_cancel h)

/-- The one-dimensional O(1) error in Lemma 2.4 can be bounded by one,
uniformly in the modulus, residue and nonnegative real radius. -/
theorem line_card_error {q : ℕ} (hq : 0 < q) (a : ℤ) {T : ℝ} (hT : 0 ≤ T) :
    |((line q a T).card : ℝ) - 2*T/q| ≤ 1 := by
  let lo := (-T-(a:ℝ))/q
  let hi := (T-(a:ℝ))/q
  have hp : (0:ℝ) < q := by exact_mod_cast hq
  have hle : lo ≤ hi := div_le_div_of_nonneg_right (by linarith) hp.le
  have hI : ⌈lo⌉ ≤ ⌊hi⌋ + 1 := by
    apply Int.ceil_le.mpr
    push_cast
    exact hle.trans (Int.lt_floor_add_one hi).le
  have hc := Int.card_Icc_of_le _ _ hI
  have hc' : ((line q a T).card : ℝ) = (⌊hi⌋ : ℝ) + 1 - (⌈lo⌉ : ℝ) := by
    rw [line_card q hq]
    exact_mod_cast hc
  have he : hi-lo = 2*T/q := by dsimp [lo,hi]; ring
  rw [hc', ← he, abs_le]
  constructor <;> linarith only [Int.floor_le hi, Int.le_ceil lo,
    Int.lt_floor_add_one hi, Int.ceil_lt_add_one lo]

/-- Cartesian product of the coordinate progressions. -/
def square (q : ℕ) (a : Point) (T : ℝ) : Finset Point :=
  Fintype.piFinset (fun i => line q (a i) T)

theorem mem_square {q : ℕ} (hq : 0 < q) (a w : Point) (T : ℝ) :
    w ∈ square q a T ↔ ∀ i, |(w i : ℝ)| ≤ T ∧ (q : ℤ) ∣ w i - a i := by
  simp only [square, Fintype.mem_piFinset, mem_line hq]

/-- A uniform error bound for the lattice-point estimate preceding partial summation.
Removing the possible origin increases the error bound by at most one. -/
theorem square_card_error {q : ℕ} (hq : 0 < q) (a : Point) {T : ℝ} (hT : 0 ≤ T) :
    |((square q a T).card : ℝ) - (2*T/q)^2| ≤ 2*(2*T/q)+1 := by
  let s := 2*T/q
  have hs : 0 ≤ s := by dsimp [s]; positivity
  let a₀ : ℝ := (line q (a 0) T).card
  let a₁ : ℝ := (line q (a 1) T).card
  have h₀ : |a₀-s| ≤ 1 := line_card_error hq _ hT
  have h₁ : |a₁-s| ≤ 1 := line_card_error hq _ hT
  have hc : ((square q a T).card : ℝ) = a₀*a₁ := by
    simp [square, Fintype.card_piFinset, Fin.prod_univ_two, a₀, a₁]
  rw [hc]
  change |a₀*a₁ - s^2| ≤ 2*s+1
  rw [show a₀*a₁ - s^2 = s*(a₀-s) + s*(a₁-s) + (a₀-s)*(a₁-s) by ring]
  calc
    _ ≤ (|s*(a₀-s)| + |s*(a₁-s)|) + |(a₀-s)*(a₁-s)| := (abs_add_le _ _).trans
      (add_le_add_left (abs_add_le _ _) _)
    _ ≤ 2*s+1 := by
      simp only [abs_mul, abs_of_nonneg hs]
      nlinarith only [mul_le_mul_of_nonneg_left h₀ hs, mul_le_mul_of_nonneg_left h₁ hs,
        mul_le_mul h₀ h₁ (abs_nonneg _) zero_le_one]

/-- Exact Möbius expansion of the primitive-vector indicator; the value at the
origin is also correct since zero has an empty divisor finset. -/
theorem primitive_indicator (w : Point) :
    (if Nat.Coprime (w 0).natAbs (w 1).natAbs then (1:ℤ) else 0) =
    ∑ j ∈ (Nat.gcd (w 0).natAbs (w 1).natAbs).divisors, ArithmeticFunction.moebius j := by
  classical
  symm
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta]
  simp [Nat.Coprime, ArithmeticFunction.one_apply]

end RTS.Lifting
