module

public import RTS.WeightQuotient
public import RTS.CardinalityUpper
public import RTS.WeightStatement
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace RTS.Dyadic

/-- Interpolate the radii 2^(dm) by flooring the base-two logarithm divided by d.
The constant can be taken to be (8d log 2)^(-d). -/
theorem exists_log_scale (d : ℕ) (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∃ m : ℕ, 0 < m ∧ (2 : ℝ) ^ (d*m) ≤ N ∧
        c * (Real.log N)^d ≤ ((m : ℝ)/4)^d := by
  let L := (d : ℝ) * Real.log 2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hL : 0 < L := mul_pos hd' h2
  refine ⟨(1 / (8*L))^d, by positivity, Real.exp (2*L),
    Real.one_le_exp (by positivity), ?_⟩
  intro N hN
  have hpos : 0 < N := (Real.exp_pos _).trans_le hN
  have hlog := (Real.le_log_iff_exp_le hpos).2 hN
  let x := Real.log N / L
  have hx : 2 ≤ x := (le_div_iff₀ hL).2 hlog
  have hx0 : 0 ≤ x := by linarith
  let m := ⌊x⌋₊
  have hm : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hx' : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
  refine ⟨m, (Nat.one_le_floor_iff x).2 (by linarith), ?_, ?_⟩
  · apply (Real.log_le_log_iff (by positivity) hpos).mp
    rw [Real.log_pow, Nat.cast_mul]
    have hh := (le_div_iff₀ hL).1 hm
    dsimp [L] at hh
    linarith only [show (d : ℝ) * m * Real.log 2 = m * (d * Real.log 2) by ring, hh]
  · rw [← mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (by positivity) (by linarith only [hlog,hL])) _ d
    have hxmul : x * L = Real.log N := div_mul_cancel₀ _ hL.ne'
    rw [← hxmul]
    have he : 1 / (8 * L) * (x * L) = x / 8 := by field_simp
    rw [he]
    linarith only [hx,hx']

/-- The isotropic block lengths yield the logarithmic lower bound. A single long
block yields the exact-cardinality lower bound in the same dimension. -/
theorem trigonometricGrowth_of_dyadic
    (h : ∀ {d : ℕ} (m : Fin d → ℕ), (∀ l, 0 < m l) →
      ∀ eligible : (Freq d →₀ ℂ) → Prop, eligible (data m) →
        ENNReal.ofReal (∏ l, factor (m l)) ≤ perBest .mt eligible) :
    TrigonometricGrowth := by
  classical
  intro d hd
  constructor
  · obtain ⟨c, hc, N₀, hN₀, hs⟩ := exists_log_scale d hd
    refine ⟨c, hc, N₀, hN₀, ?_⟩
    intro N hN
    obtain ⟨m, hm, hb, hl⟩ := hs N hN
    have hel := data_in_box (fun _ : Fin d => m) (N := N) (by simpa using hb)
    have hper := h (fun _ : Fin d => m) (fun _ => hm) (perInBox N) hel
    have hm' : ((m : ℝ)/4)^d ≤ (factor m)^d :=
      pow_le_pow_left₀ (by positivity) (quarter_le_dyadic_ratio m hm) d
    have hbound : ENNReal.ofReal (c * (Real.log N)^d) ≤ perMT d N :=
      (ENNReal.ofReal_le_ofReal (hl.trans hm')).trans (by simpa [perMT] using hper)
    exact ⟨hbound.trans (perMT_le_perStein d N), hbound⟩
  · refine ⟨1/4, 1, by norm_num, by norm_num, 1, le_rfl, ?_⟩
    intro n hn
    let i₀ : Fin d := ⟨0, hd⟩
    let m (i : Fin d) := if i = i₀ then n else 1
    have hm : ∀ i, 0 < m i := fun i => by dsimp [m]; split <;> omega
    have hprod : ∏ i, m i = n := Fintype.prod_ite_eq' i₀ (fun _ => n)
    have hfac : ∏ i, factor (m i) = factor n := by
      simp only [m, apply_ite factor, factor_one]
      exact Fintype.prod_ite_eq' i₀ (fun _ => factor n)
    have hel : (data m).support.card = n := (data_card m).trans hprod
    have hper := h m hm (fun a => a.support.card = n) hel
    rw [hfac] at hper
    have hr : (1/4 : ℝ)*n ≤ factor n := by
      simpa only [factor, one_div, div_eq_inv_mul, mul_one] using quarter_le_dyadic_ratio n hn
    have hbound : ENNReal.ofReal ((1/4 : ℝ)*n) ≤ perMTCard d n :=
      (ENNReal.ofReal_le_ofReal hr).trans hper
    have hu : perSteinCard d n ≤ ENNReal.ofReal (1*(n:ℝ)) := by
      simpa only [one_mul, ENNReal.ofReal_natCast] using perSteinCard_le_card d n
    exact ⟨hbound.trans (perMTCard_le_perSteinCard d n), hbound, hu,
      (perMTCard_le_perSteinCard d n).trans hu⟩

end RTS.Dyadic
