module

public import RTS.LiftingAbel

/-! A uniform quantitative lower bound after the coprimality sieve. The leading
Möbius term suffices because the reciprocal squares starting at two sum to at
most three quarters. -/

@[expose] public noncomputable section
namespace RTS.Lifting
open Finset

theorem reciprocal_square_tail (N : ℕ) :
    (∑ j ∈ Icc 2 N, 1/(j:ℝ)^2) ≤ 3/4 := by
  by_cases hN : 2 ≤ N
  · suffices h : (∑ j ∈ Icc 2 N, 1/(j:ℝ)^2) ≤ 3/4-1/(N:ℝ) by
      exact h.trans (sub_le_self _ (by positivity))
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast
      have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      have inc : 1/(n+1:ℝ)^2 ≤ 1/(n:ℝ)-1/(n+1) := by
        field_simp
        nlinarith
      linarith
  · simp [Finset.Icc_eq_empty_of_lt (by omega : N < 2)]; norm_num

/-- A per-residue lower bound for the entire Möbius sum, requiring no
prime-distribution input. The representative at each invertible divisor may be arbitrary. -/
theorem moebius_sum_lower {q : ℕ} (hq : 0 < q) (b : ℕ → Point) {T : ℝ} (hT : 1 ≤ T) :
    2*Real.log T/(q:ℝ)^2 - 74 ≤
    ∑ j ∈ (Icc 1 ⌊T⌋₊).filter (fun j => j.Coprime q),
      ((ArithmeticFunction.moebius j : ℤ) : ℝ)/(j:ℝ)^2 * inverseSquareSum q (b j) (T/j) := by
  let S := (Icc 1 ⌊T⌋₊).filter (fun j => j.Coprime q)
  let M := 8*Real.log T/(q:ℝ)^2
  have hM : 0 ≤ M := by dsimp [M]; exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hT)) (sq_nonneg _)
  have h1 : 1 ∈ S := by simp [S, Nat.one_le_floor_iff, hT]
  have hv (j : ℕ) (hj : j ∈ S.erase 1) :
      ((ArithmeticFunction.moebius j : ℤ):ℝ)/(j:ℝ)^2 * inverseSquareSum q (b j) (T/j) ≥
      -(M+42)*(1/(j:ℝ)^2) := by
    have bounds := mem_Icc.mp (mem_filter.mp (mem_erase.mp hj).2).1
    have hj' : 1 ≤ (j:ℝ) := by exact_mod_cast bounds.1
    have hjT : (j:ℝ) ≤ T := (Nat.le_floor_iff (by linarith)).mp bounds.2
    have hjp : 0 < (j:ℝ) := by linarith
    have hT' : 1 ≤ T/j := (one_le_div hjp).2 hjT
    have H := (abs_le.mp (inverseSquareSum_error hq (b j) hT')).2
    have hlog : Real.log (T/j) ≤ Real.log T :=
      Real.log_le_log (by linarith) (div_le_self (by linarith) hj')
    have hs : inverseSquareSum q (b j) (T/j) ≤ M+42 := by
      have : 8*Real.log (T/j)/(q:ℝ)^2 ≤ M :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by norm_num)) (sq_nonneg _)
      linarith
    have hs₀ : 0 ≤ inverseSquareSum q (b j) (T/j) := sum_nonneg fun _ _ => by positivity
    have hμ := (abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := j))).1
    have hμ' : (-1:ℝ) ≤ (ArithmeticFunction.moebius j : ℤ) := by exact_mod_cast hμ
    have hbase := mul_le_mul_of_nonneg_right hμ' hs₀
    have hf : -(M+42) ≤ (ArithmeticFunction.moebius j : ℤ)*inverseSquareSum q (b j) (T/j) := by linarith
    simpa only [div_mul_eq_mul_div, mul_one_div] using div_le_div_of_nonneg_right hf (sq_nonneg _)
  have htail : (∑ j ∈ S.erase 1, 1/(j:ℝ)^2) ≤ 3/4 := by
    apply le_trans _ (reciprocal_square_tail ⌊T⌋₊)
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    intro j hj
    obtain ⟨hne,hi⟩ := mem_erase.mp hj
    obtain ⟨hl,hu⟩ := mem_Icc.mp (mem_filter.mp hi).1
    exact mem_Icc.mpr ⟨by omega,hu⟩
  have hsum := Finset.sum_le_sum hv
  rw [← Finset.mul_sum] at hsum
  have hlow := (abs_le.mp (inverseSquareSum_error hq (b 1) hT)).1
  rw [← sum_erase_add _ _ h1]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one, one_pow,
    div_one, one_mul]
  have hminor := mul_le_mul_of_nonneg_left htail (show 0 ≤ M+42 by positivity)
  change -(42:ℝ) ≤ inverseSquareSum q (b 1) T - M at hlow
  rw [show 2*Real.log T/(q:ℝ)^2 = M/4 by dsimp [M]; ring]
  linarith

end RTS.Lifting
