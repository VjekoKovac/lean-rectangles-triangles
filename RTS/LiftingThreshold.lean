module

public import RTS.PrimitiveSieve
public import RTS.LiftingSieveBounds

/-! # Explicit uniform threshold for the lattice bounds

The weaker absolute coefficients used here suffice for the asymptotic theorem.
The choice `1000` is only for absorption of errors, uniformly in the modulus.
-/
@[expose] public section
namespace RTS.Lifting
open Real

theorem primitive_inverseSquare_lower {q : ℕ} (hq : 0 < q) (a : Point)
    (ha : (content a).Coprime q) {T : ℝ} (hT : 1 ≤ T) :
    2 * log T / (q : ℝ)^2 - 74 ≤ primitiveInverseSquareSum q a T := by
  rw [primitive_inverseSquare_expansion hq a ha T]
  exact moebius_sum_lower hq (fun j => invRep j q a) hT

private theorem threshold_core {q : ℕ} (hq : 0 < q) {N : ℝ}
    (hN : exp (1000*(q:ℝ)^2) ≤ N) :
    8*(q:ℝ) ≤ N ∧ 1000*(q:ℝ)^2 ≤ log N := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h8 : 8 * (q : ℝ) ≤ 1 + 1000 * (q : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq₁) (by positivity : 0 ≤ (q : ℝ))]
  exact ⟨h8.trans ((add_one_le_exp _ |>.trans' (le_of_eq (add_comm ..))).trans hN),
    by simpa using log_le_log (exp_pos _) hN⟩

theorem lifting_threshold {q : ℕ} (hq : 0 < q) {N : ℝ}
    (hN : exp (1000*(q:ℝ)^2) ≤ N) :
    1 ≤ N/(8*q) ∧ 1 ≤ N/(4*q) ∧ 4 ≤ N ∧
    log N/(2*(q:ℝ)^2) ≤ 2*log (N/(8*q))/(q:ℝ)^2 - 74 := by
  obtain ⟨h8,hlog⟩ := threshold_core hq hN
  have hp : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (q:ℝ) ≤ (q:ℝ)^2 := by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hq₁)]
  have hNpos : 0 < N := by linarith
  refine ⟨(one_le_div (by positivity)).mpr h8,
    (one_le_div (by positivity)).mpr (by linarith), by linarith, ?_⟩
  rw [log_div hNpos.ne' (by positivity)]
  have hlogq : log (8*(q:ℝ)) ≤ 8*(q:ℝ) := (log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  field_simp
  rw [mul_comm (q : ℝ) 8]
  nlinarith

theorem lifting_upper_threshold {q : ℕ} (hq : 0 < q) {N : ℝ}
    (hN : exp (1000*(q:ℝ)^2) ≤ N) :
    128*(N/q)^2*(8*log (4*N)/(q:ℝ)^2+42) + 2*(9*N/q)^2 ≤
      10000*N^2*log N/(q:ℝ)^4 := by
  obtain ⟨h8,hlog⟩ := threshold_core hq hN
  have hp : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hNpos : 0 < N := by linarith
  have h4 : log (4*N) ≤ 2*log N := by
    rw [log_mul (by norm_num) hNpos.ne']
    linarith [log_le_log (by norm_num : (0:ℝ) < 4) (by linarith : 4 ≤ N)]
  have hnum : 128*(8*log (4*N) + 42*(q:ℝ)^2) + 162*(q:ℝ)^2 ≤ 10000*log N := by
    linarith [sq_nonneg (q:ℝ)]
  calc
    _ = (N^2/(q:ℝ)^4) * (128*(8*log (4*N) + 42*(q:ℝ)^2) + 162*(q:ℝ)^2) := by
      field_simp
      ring
    _ ≤ (N^2/(q:ℝ)^4) * (10000*log N) := mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by ring

end RTS.Lifting
