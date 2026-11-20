module

public import RTS.AnalysisDefs

/-! The Stein denominator is bounded above by the MT denominator. Taking an infimum
over admissible constants reverses the inclusion of their admissible sets. -/

@[expose] public section

namespace RTS

open scoped ENNReal BigOperators

theorem perRHS_stein_le_mt {d : ℕ} (a : Freq d →₀ ℂ)
    (w : Torus d × UnitAddCircle → ℝ) :
    perRHS .stein a w ≤ perRHS .mt a w := by
  classical
  unfold perRHS
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun k hk =>
    mul_le_mul_right (le_iSup (fun j : ↥a.support => ⨆ x, perXray w x j) ⟨k,hk⟩) _

theorem perMTAdmissible_of_stein {d : ℕ} {eligible : (Freq d →₀ ℂ) → Prop}
    {C : ℝ≥0∞} (hC : perAdmissible .stein eligible C) : perAdmissible .mt eligible C := by
  intro a ha w hw
  exact (hC a ha w hw).trans (mul_le_mul_right (perRHS_stein_le_mt a w) C)

theorem perBest_mt_le_stein {d : ℕ} (eligible : (Freq d →₀ ℂ) → Prop) :
    perBest .mt eligible ≤ perBest .stein eligible :=
  sInf_le_sInf fun _ hC => perMTAdmissible_of_stein hC

theorem perMT_le_perStein (d : ℕ) (N : ℝ) : perMT d N ≤ perStein d N :=
  perBest_mt_le_stein _

theorem perMTCard_le_perSteinCard (d n : ℕ) : perMTCard d n ≤ perSteinCard d n :=
  perBest_mt_le_stein _

end RTS
