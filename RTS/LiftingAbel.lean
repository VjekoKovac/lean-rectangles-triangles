module

public import RTS.LiftingCounts
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.FieldSimp

/-! A discrete partial-summation bound for the inverse-square weight in Lemma 2.4.
It retains the leading coefficient of the logarithm and has a uniform absolute error. -/

@[expose] public noncomputable section
namespace RTS.Lifting
open Finset

/-- Square-shell radius, including the origin at radius zero. -/
def radius (w : Point) : ℕ := max (w 0).natAbs (w 1).natAbs

def nonzeroSquare (q : ℕ) (a : Point) (X : ℝ) := (square q a X).erase 0

theorem radius_le_iff (w : Point) (T : ℝ) :
    (radius w : ℝ) ≤ T ↔ ∀ i, |(w i : ℝ)| ≤ T := by
  simp only [radius, Nat.cast_max, max_le_iff, Fin.forall_fin_two]
  have he (z : ℤ) : (z.natAbs : ℝ) = |(z:ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; simp
  simp only [he]

theorem nonzeroSquare_card_error {q : ℕ} (hq : 0 < q) (a : Point) {T : ℝ} (hT : 0 ≤ T) :
    |((nonzeroSquare q a T).card : ℝ) - 4*T^2/(q:ℝ)^2| ≤ 4*T/q + 2 := by
  have h := square_card_error hq a hT
  unfold nonzeroSquare
  rw [show 4*T^2/(q:ℝ)^2 = (2*T/q)^2 by ring]
  rw [show 4*T/q = 2*(2*T/q) by ring]
  by_cases h₀ : 0 ∈ square q a T
  · have hcnt := Finset.card_erase_add_one h₀
    have hc : (((square q a T).erase 0).card : ℝ) + 1 = (square q a T).card := by exact_mod_cast hcnt
    rw [abs_le] at h ⊢
    constructor <;> linarith
  · rw [erase_eq_of_notMem h₀]
    linarith

/-- The weighted sum over integer points of a residue class in the sup-norm ball. -/
def inverseSquareSum (q : ℕ) (a : Point) (T : ℝ) : ℝ :=
  ∑ w ∈ nonzeroSquare q a T, 1/(radius w : ℝ)^2

theorem radius_pos {w : Point} (hw : w ≠ 0) : 0 < radius w := by
  by_contra! h
  apply hw
  have he : w 0 = 0 ∧ w 1 = 0 := by simpa [radius] using h
  funext i
  fin_cases i <;> aesop

private theorem shell_step {q : ℕ} (hq : 0 < q) (a : Point) (n : ℕ) :
    inverseSquareSum q a (n+1) = inverseSquareSum q a n +
      (((nonzeroSquare q a (n+1)).card : ℝ) - (nonzeroSquare q a n).card)/(n+1:ℝ)^2 := by
  let S := nonzeroSquare q a (n+1)
  let R := nonzeroSquare q a n
  have hsub : R ⊆ S := by
    intro w hw
    obtain ⟨hn, h⟩ := mem_erase.mp hw
    exact mem_erase.mpr ⟨hn, (mem_square hq ..).mpr fun i =>
      ⟨((mem_square hq ..).mp h i).1.trans (by linarith), ((mem_square hq ..).mp h i).2⟩⟩
  have hrad (w : Point) (hw : w ∈ S \ R) : radius w = n+1 := by
    obtain ⟨hs,hr⟩ := mem_sdiff.mp hw
    obtain ⟨h0, hs'⟩ := mem_erase.mp hs
    have hb := (mem_square hq ..).mp hs'
    have hle : (radius w : ℝ) ≤ n+1 := (radius_le_iff ..).mpr fun i => (hb i).1
    have hgt : ¬ (radius w : ℝ) ≤ n := fun he => hr (mem_erase.mpr ⟨h0,
      (mem_square hq ..).mpr fun i => ⟨(radius_le_iff ..).mp he i, (hb i).2⟩⟩)
    have hle' : radius w ≤ n+1 := by exact_mod_cast hle
    have hgt' : ¬ radius w ≤ n := by exact_mod_cast hgt
    omega
  have hsum := Finset.sum_sdiff hsub (f := fun w => 1/(radius w : ℝ)^2)
  change (∑ w ∈ S, 1/(radius w : ℝ)^2) = (∑ w ∈ R, 1/(radius w : ℝ)^2) +
    ((S.card:ℝ)-R.card)/(n+1:ℝ)^2
  rw [← hsum, add_comm]
  congr 1
  calc
    _ = ∑ _w ∈ S \ R, 1/(n+1 : ℝ)^2 := sum_congr rfl fun w hw => by rw [hrad w hw]; push_cast; rfl
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
      ring

/-- Error for advancing one shell in Abel summation. The telescoping majorant is
16 times (1/m − 1/(m+1)). -/
private theorem abel_step_bound {b m C : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 4)
    (hm : 1 ≤ m) (he : |C - b*m^2| ≤ 6*m) :
    |C*(1/m^2-1/(m+1)^2)-2*b/(m+1)| ≤ 16*(1/m-1/(m+1)) := by
  have hm' : 0 < m := by linarith
  have hm1 : 0 < m+1 := by linarith
  let δ := 1/m-1/(m+1)
  have hd : δ = 1/(m*(m+1)) := by dsimp [δ]; field_simp; ring
  have hd0 : 0 ≤ δ := by rw [hd]; positivity
  have hfac : 1/m^2-1/(m+1)^2 = δ*(1/m+1/(m+1)) := by dsimp [δ]; field_simp; ring
  have hmain : C*(1/m^2-1/(m+1)^2)-2*b/(m+1) =
      (C-b*m^2)*(1/m^2-1/(m+1)^2)-b/(m+1)^2 := by field_simp; ring
  have hsum : 1/m + 1/(m+1) ≤ 2/m := by
    have := one_div_le_one_div_of_le hm' (show m ≤ m+1 by linarith)
    rw [show 2/m = 1/m+1/m by ring]
    linarith
  have hmax : b/(m+1)^2 ≤ 4*δ := by
    rw [hd]
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ 4-b by linarith) hm'.le]
  rw [hmain, hfac]
  calc
    _ ≤ |C-b*m^2| * (δ*(1/m+1/(m+1))) + b/(m+1)^2 := by
      let U := C-b*m^2
      let V := δ*(1/m+1/(m+1))
      have hv : 0 ≤ V := by dsimp [V]; positivity
      have hU := abs_le.mp (le_refl |U|)
      have h₁ := mul_le_mul_of_nonneg_right hU.1 hv
      have h₂ := mul_le_mul_of_nonneg_right hU.2 hv
      change |U*V-b/(m+1)^2| ≤ |U| * V+b/(m+1)^2
      rw [abs_le]
      constructor <;> nlinarith [show 0 ≤ b/(m+1)^2 by positivity]
    _ ≤ (6*m) * (δ*(2/m)) + 4*δ :=
      add_le_add (mul_le_mul he (mul_le_mul_of_nonneg_left hsum hd0)
        (by positivity) (by positivity)) hmax
    _ = _ := by change _ = 16*δ; field_simp; ring

/-- The partial-summation estimate before removing the harmonic number. -/
private theorem corrected_sum_bound {q : ℕ} (hq : 0 < q) (a : Point) (n : ℕ) (hn : 1 ≤ n) :
    let C (m : ℕ) : ℝ := (nonzeroSquare q a m).card
    let b := 4/(q:ℝ)^2
    |inverseSquareSum q a n - C n/(n:ℝ)^2 - 2*b*(harmonic n : ℝ)| ≤
      2*b + 16*(1-1/(n:ℝ)) := by
  let C (m : ℕ) : ℝ := (nonzeroSquare q a m).card
  let b := 4/(q:ℝ)^2
  let F (m : ℕ) := inverseSquareSum q a m - C m/(m:ℝ)^2 - 2*b*(harmonic m : ℝ)
  change |F n| ≤ 2*b + 16*(1-1/(n:ℝ))
  have hp : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hbpos : 0 ≤ b := by dsimp [b]; positivity
  have hbmax : b ≤ 4 := by dsimp [b]; apply div_le_self (by norm_num); nlinarith
  induction n, hn using Nat.le_induction with
  | base =>
    have empty : nonzeroSquare q a 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hz, hs⟩ := mem_erase.mp hw
      have hh := (radius_le_iff w 0).mpr fun i => ((mem_square hq ..).mp hs i).1
      exact (show (0:ℝ) < radius w by exact_mod_cast radius_pos hz).not_ge hh
    have he := shell_step hq a 0
    simp only [Nat.cast_zero, zero_add, empty, Finset.card_empty, Nat.cast_one, one_pow,
      sub_zero, div_one] at he
    have hz : inverseSquareSum q a 0 = 0 := by simp [inverseSquareSum,empty]
    simp [F, C, he, hz, harmonic_succ, abs_of_nonneg hbpos]
  | succ n hn ih =>
    let m : ℝ := n
    have hpos : 1 ≤ m := by dsimp [m]; exact_mod_cast hn
    have he : |C n-b*m^2| ≤ 6*m := by
      have hh := nonzeroSquare_card_error hq a (Nat.cast_nonneg (α:=ℝ) n)
      have hd : 4*m/(q:ℝ) ≤ 4*m := div_le_self (by positivity) hp
      change |C n-4*m^2/(q:ℝ)^2| ≤ _ at hh
      dsimp only [b]
      rw [show 4/(q:ℝ)^2*m^2 = 4*m^2/(q:ℝ)^2 by ring]
      linarith
    have hf : F (n+1) - F n = C n*(1/m^2 - 1/(m+1)^2) - 2*b/(m+1) := by
      have hh := shell_step hq a n
      simp only [F, Nat.cast_add, Nat.cast_one, harmonic_succ, Rat.cast_add, Rat.cast_inv,
        Rat.cast_natCast] 
      rw [hh]
      dsimp [m,C]
      push_cast
      ring
    have hh := abel_step_bound hbpos hbmax hpos he
    rw [← hf] at hh
    have ht := abs_add_le (F (n+1)-F n) (F n)
    rw [sub_add_cancel] at ht
    change |F n| ≤ 2*b+16*(1-1/m) at ih
    change |F (n+1)| ≤ 2*b+16*(1-1/((n+1:ℕ):ℝ))
    push_cast
    change |F (n+1)| ≤ 2*b+16*(1-1/(m+1))
    linarith

private theorem square_at_floor {q : ℕ} (hq : 0 < q) (a : Point) (T : ℝ) (hT : 0 ≤ T) :
    nonzeroSquare q a (⌊T⌋₊ : ℝ) = nonzeroSquare q a T := by
  apply congrArg (fun S : Finset Point => S.erase 0)
  ext w
  simp only [mem_square hq, forall_and, ← radius_le_iff]
  exact and_congr_left fun _ => by rw [Nat.cast_le, Nat.le_floor_iff hT]

/-- For every positive modulus and every residue, the inverse-square sum differs
from 8 log(T)/q² by at most 42. The bound is uniform even when T is real. -/
theorem inverseSquareSum_error {q : ℕ} (hq : 0 < q) (a : Point) {T : ℝ} (hT : 1 ≤ T) :
    |inverseSquareSum q a T - 8*Real.log T/(q:ℝ)^2| ≤ 42 := by
  let n := ⌊T⌋₊
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).2 hT
  have hr : (1:ℝ) ≤ n := by exact_mod_cast hn
  let C : ℝ := (nonzeroSquare q a (n:ℝ)).card
  let b := 4/(q:ℝ)^2
  have hp : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbmax : b ≤ 4 := by dsimp [b]; apply div_le_self (by norm_num); nlinarith
  have hcorr := corrected_sum_bound hq a n hn
  change |inverseSquareSum q a n - C/(n:ℝ)^2 - 2*b*(harmonic n:ℝ)| ≤
    2*b+16*(1-1/(n:ℝ)) at hcorr
  have h₀ : C/(n:ℝ)^2 ≤ 10 := by
    have hh := (abs_le.mp (nonzeroSquare_card_error hq a (Nat.cast_nonneg (α:=ℝ) n))).2
    change C-4*(n:ℝ)^2/(q:ℝ)^2 ≤ _ at hh
    have he : 4*(n:ℝ)/(q:ℝ) ≤ 4*(n:ℝ) := div_le_self (by positivity) hp
    have he' : 4*(n:ℝ)^2/(q:ℝ)^2 ≤ 4*(n:ℝ)^2 :=
      div_le_self (by positivity) (by nlinarith)
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [show (0:ℝ) ≤ (n:ℝ)*((n:ℝ)-1) by positivity]
  have hcs : 0 ≤ C/(n:ℝ)^2 := by dsimp [C]; positivity
  have hh₁ : Real.log T ≤ (harmonic n:ℝ) := log_le_harmonic_floor T (by linarith)
  have hh₂ : (harmonic n:ℝ) ≤ 1+Real.log T := harmonic_floor_le_one_add_log T hT
  have hH : |2*b*((harmonic n:ℝ)-Real.log T)| ≤ 8 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hb (show 0 ≤ 1+Real.log T-(harmonic n:ℝ) by linarith)]
  have hred : inverseSquareSum q a T = inverseSquareSum q a n := by
    dsimp [inverseSquareSum, n]; rw [square_at_floor hq a T (by linarith)]
  rw [hred, show 8*Real.log T/(q:ℝ)^2 = 2*b*Real.log T by dsimp [b]; ring]
  rw [abs_le] at hcorr hH ⊢
  have he : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
  constructor <;> nlinarith

end RTS.Lifting
