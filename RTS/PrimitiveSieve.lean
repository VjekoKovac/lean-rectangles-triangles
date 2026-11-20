module

public import RTS.LiftingAbel
public import RTS.LiftingResidues
public import Mathlib.Tactic

/-! # The finite Möbius change of variables for primitive lattice directions

The content of a nonzero vector is the gcd of its two absolute coordinates.
The proof filters by its divisors, exchanges two finite sums, and writes
`w = j z` in each term. The residue of `z` is computed in the composite ring
`ZMod q`, using only the invertibility of the divisor `j` modulo `q`.
-/

@[expose] public noncomputable section
namespace RTS.Lifting
open Finset

def content (w : Point) : ℕ := (w 0).natAbs.gcd (w 1).natAbs

def primitiveInverseSquareSum (q : ℕ) (a : Point) (T : ℝ) : ℝ :=
  ∑ w ∈ (nonzeroSquare q a T).filter (fun w => content w = 1), 1/(radius w : ℝ)^2

def invRep (j q : ℕ) (a : Point) : Point :=
  fun i => (((j : ZMod q)⁻¹ * (a i : ZMod q)).val : ℤ)

private def dilate (j : ℕ) (z : Point) : Point := fun i => (j : ℤ) * z i

private theorem dilate_inj {j : ℕ} (hj : 0 < j) : Function.Injective (dilate j) := by
  intro v w h
  funext i
  exact mul_left_cancel₀ (by exact_mod_cast hj.ne' : (j:ℤ) ≠ 0) (congrFun h i)

private theorem radius_dilate (j : ℕ) (z : Point) :
    radius (dilate j z) = j * radius z := by
  simp [radius, dilate, Int.natAbs_mul, Nat.mul_max_mul_left]

private theorem content_dvd {j : ℕ} (w : Point) :
    j ∣ content w ↔ ∀ i, (j : ℤ) ∣ w i := by
  simp [content, Fin.forall_fin_two, ← Nat.dvd_gcd_iff, Int.natCast_dvd]

private theorem content_pos {w : Point} (hw : w ≠ 0) : 0 < content w := by
  by_contra! h
  apply hw
  have h0 : w 0 = 0 ∧ w 1 = 0 := by simpa [content] using h
  funext i
  fin_cases i <;> aesop

private theorem content_le_radius (w : Point) : content w ≤ radius w := by
  by_cases h : (w 0).natAbs = 0
  · simp [content, radius, h]
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (Nat.gcd_dvd_left ..)).trans (le_max_left ..)

private theorem mem_nonzero_square {q : ℕ} (hq : 0 < q) (a w : Point) (T : ℝ) :
    w ∈ nonzeroSquare q a T ↔
      w ≠ 0 ∧ (radius w : ℝ) ≤ T ∧ reduce q w = reduce q a := by
  simp only [nonzeroSquare, mem_erase, mem_square hq, radius_le_iff, reduce, funext_iff,
    ZMod.intCast_eq_intCast_iff_dvd_sub, forall_and]
  exact and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => by
    rw [← dvd_neg, neg_sub]

private theorem divisor_coprime {q : ℕ} (hq : 0 < q) (a : Point)
    (ha : (content a).Coprime q) {w : Point} {T : ℝ} (hw : w ∈ nonzeroSquare q a T)
    {j : ℕ} (hj : j ∣ content w) : j.Coprime q := by
  by_contra hn
  obtain ⟨p, hp, hpj, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  apply Nat.Prime.not_coprime_iff_dvd.mpr _ ha
  refine ⟨p,hp,(content_dvd a).mpr ?_,hpq⟩
  intro i
  have hpw := (content_dvd w).mp (hpj.trans hj) i
  have hqa := ((mem_square hq a w T).mp (mem_erase.mp hw).2 i).2
  have hpq' : (p:ℤ) ∣ (q:ℤ) := by exact_mod_cast hpq
  simpa using dvd_sub hpw (hpq'.trans hqa)

private theorem dilate_membership {q j : ℕ} (hq : 0 < q) (hj : 0 < j) (hc : j.Coprime q)
    (a z : Point) (T : ℝ) :
    dilate j z ∈ nonzeroSquare q a T ↔ z ∈ nonzeroSquare q (invRep j q a) (T/j) := by
  have : NeZero q := ⟨hq.ne'⟩
  have hi : IsUnit (j : ZMod q) := (ZMod.isUnit_iff_coprime j q).mpr hc
  have hz : dilate j z ≠ 0 ↔ z ≠ 0 := by
    have h0 : dilate j 0 = 0 := by ext; simp [dilate]
    simpa only [h0] using ((dilate_inj hj).ne_iff (x := z) (y := 0))
  have hdiv : ((j * radius z : ℕ) : ℝ) ≤ T ↔ (radius z : ℝ) ≤ T/j := by
    rw [le_div_iff₀ (by exact_mod_cast hj : (0:ℝ) < j), Nat.cast_mul, mul_comm]
  simp only [mem_nonzero_square hq, hz, radius_dilate, hdiv, and_congr_right_iff]
  intro _ _
  simp only [reduce, funext_iff, dilate, Int.cast_mul, Int.cast_natCast, invRep, ZMod.natCast_zmod_val]
  apply forall_congr'
  intro i
  constructor
  · intro he
    rw [← he, ← mul_assoc, ZMod.inv_mul_of_unit _ hi, one_mul]
  · intro he
    rw [he, ← mul_assoc, ZMod.mul_inv_of_unit _ hi, one_mul]

private theorem dilates_eq_filter {q j : ℕ} (hq : 0 < q) (hj : 0 < j) (hc : j.Coprime q)
    (a : Point) (T : ℝ) :
    ((nonzeroSquare q (invRep j q a) (T/j)).image (dilate j)) =
      (nonzeroSquare q a T).filter (fun w => j ∣ content w) := by
  ext w
  constructor
  · rintro hw
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨(dilate_membership hq hj hc a z T).mpr hz,
      (content_dvd _).mpr fun i => dvd_mul_right _ _⟩
  · intro hw
    obtain ⟨hw,hj'⟩ := mem_filter.mp hw
    choose z hz using (content_dvd w).mp hj'
    have he : dilate j z = w := funext fun i => (hz i).symm
    exact mem_image.mpr ⟨z,(dilate_membership hq hj hc a z T).mp (he ▸ hw),he⟩

/-- Finite Möbius expansion of the primitive inverse-square sum, uniform in the
real radius. Coordinates of the residue vector do not share a prime divisor with `q`. -/
theorem primitive_inverseSquare_expansion {q : ℕ} (hq : 0 < q) (a : Point)
    (ha : (content a).Coprime q) (T : ℝ) :
    primitiveInverseSquareSum q a T =
      ∑ j ∈ (Icc 1 ⌊T⌋₊).filter (fun j => j.Coprime q),
        ((ArithmeticFunction.moebius j : ℤ) : ℝ) / (j:ℝ)^2 *
          inverseSquareSum q (invRep j q a) (T/j) := by
  let W := nonzeroSquare q a T
  let J := (Icc 1 ⌊T⌋₊).filter (fun j => j.Coprime q)
  let M (j : ℕ) : ℝ := ArithmeticFunction.moebius j
  let wt (w : Point) : ℝ := 1/(radius w : ℝ)^2
  have hdiv (w : Point) (hw : w ∈ W) :
      J.filter (fun j => j ∣ content w) = (content w).divisors := by
    have hp := content_pos (mem_erase.mp hw).1
    have hrad := ((mem_nonzero_square hq a w T).mp hw).2.1
    ext j
    simp only [J, mem_filter, mem_Icc, Nat.mem_divisors, hp.ne', ne_eq, not_false_eq_true, and_true]
    constructor
    · exact fun h => h.2
    · intro hj
      have hj' : 0 < j := Nat.pos_of_dvd_of_pos hj hp
      refine ⟨⟨⟨hj',Nat.le_floor ?_⟩,divisor_coprime hq a ha hw hj⟩,hj⟩
      exact (show (j:ℝ) ≤ radius w by exact_mod_cast (Nat.le_of_dvd hp hj).trans (content_le_radius w)).trans hrad
  have hind (w : Point) (hw : w ∈ W) : (if content w = 1 then (1:ℝ) else 0) =
      ∑ j ∈ J.filter (fun j => j ∣ content w), M j := by
    rw [hdiv w hw]
    have he := congrArg (fun n : ℤ => (n : ℝ)) (primitive_indicator w)
    by_cases h : (w 0).natAbs.gcd (w 1).natAbs = 1 <;> simpa [content, Nat.Coprime, M, h] using he
  have hstep (j : ℕ) (hj : j ∈ J) :
      (∑ w ∈ W.filter (fun w => j ∣ content w), M j * wt w) =
        M j/(j:ℝ)^2 * inverseSquareSum q (invRep j q a) (T/j) := by
    obtain ⟨hj,hc⟩ := mem_filter.mp hj
    have hj' := (mem_Icc.mp hj).1
    rw [← dilates_eq_filter hq hj' hc a T, Finset.sum_image (fun _ _ _ _ he => dilate_inj hj' he)]
    unfold inverseSquareSum
    rw [mul_sum]
    apply sum_congr rfl
    intro z _
    simp only [wt, radius_dilate, Nat.cast_mul, mul_pow]
    ring
  change (∑ w ∈ W.filter (fun w => content w = 1), wt w) = _
  rw [sum_filter]
  calc
    _ = ∑ w ∈ W, ∑ j ∈ J, if j ∣ content w then M j * wt w else 0 := by
      apply sum_congr rfl
      intro w hw
      rw [← sum_filter, ← sum_mul, ← hind w hw]
      split_ifs <;> simp
    _ = ∑ j ∈ J, ∑ w ∈ W.filter (fun w => j ∣ content w), M j * wt w := by
      rw [sum_comm]
      simp only [sum_filter]
    _ = _ := sum_congr rfl hstep

end RTS.Lifting
