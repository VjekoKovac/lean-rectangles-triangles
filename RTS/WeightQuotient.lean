module

public import RTS.WeightTest
public import RTS.AnalysisOrder

/-! # Converting a pair of dyadic test integrals into a sharp-constant bound -/

@[expose] public section
namespace RTS.Dyadic
open Finset
open scoped ENNReal
variable {d : ℕ}

/-- The single-coordinate quotient for the floor-half choice. -/
noncomputable def factor (m : ℕ) : ℝ :=
  ((m / 2 + 1 : ℕ) : ℝ) * ((m - m/2 : ℕ) : ℝ) / m

theorem factor_one : factor 1 = 1 := by norm_num [factor]

theorem test_quotient (m : Fin d → ℕ) (hm : ∀ l, 0 < m l)
    (r : Fin d → ℕ) (hr : ∀ l, r l = m l/2) :
    (∏ l, factor (m l)) =
      ((∏ l, (r l+1)^2 * (m l).choose (r l+1) : ℕ) : ℝ) /
      (((indexBox m).card : ℝ) * (family m r).card) := by
  rw [indexBox_card, family_card]
  push_cast
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro l _
  have hh := dyadic_binomial_ratio (m l) (r l) (hm l) (by rw [hr]; omega)
  simpa [hr, factor] using hh.symm

theorem test_to_lower (m : Fin d → ℕ) (hm : ∀ l, 0 < m l)
    (eligible : (Freq d →₀ ℂ) → Prop) (hel : eligible (data m))
    (r : Fin d → ℕ) (hr : ∀ l, r l = m l/2)
    (hnum : ((∏ l, (r l + 1)^2 * (m l).choose (r l + 1) : ℕ) : ℝ≥0∞) ≤
      perLHS (data m) (weight m r))
    (hden : perRHS .mt (data m) (weight m r) ≤
      ((indexBox m).card:ℝ≥0∞) * (family m r).card) :
    ENNReal.ofReal (∏ l, factor (m l)) ≤ perBest .mt eligible := by
  apply le_sInf
  intro C hC
  have h := hnum.trans ((hC (data m) hel (weight m r) (weight_valid ..)).trans
    (mul_le_mul_right hden C))
  have hpos : 0 < (indexBox m).card * (family m r).card := by
    rw [indexBox_card, family_card]
    exact Nat.mul_pos (Finset.prod_pos (fun l _ => hm l))
      (Finset.prod_pos (fun l _ => Nat.choose_pos (by rw [hr]; omega)))
  have hR : 0 < ((indexBox m).card:ℝ) * (family m r).card := by exact_mod_cast hpos
  have hE : (((indexBox m).card:ℝ≥0∞) * (family m r).card) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [test_quotient m hm r hr, ENNReal.ofReal_div_of_pos hR,
    ENNReal.ofReal_mul (by positivity)]
  simp only [ENNReal.ofReal_natCast]
  exact (ENNReal.div_le_iff hE (ENNReal.mul_ne_top (by simp) (by simp))).2 h

end RTS.Dyadic
