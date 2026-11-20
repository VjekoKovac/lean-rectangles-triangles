module

public import RTS.AnalysisDefs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Finiteness

/-! The half-open cube and its characteristic bump for §3.1. -/
@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace RTS.Transference

variable {d : ℕ}

def originBox (d : ℕ) (r : ℝ) : Set (Space d) :=
  univ.pi (fun _ => Ioc 0 r)

theorem mem_originBox {r : ℝ} {η : Space d} :
    η ∈ originBox d r ↔ ∀ i, 0 < η i ∧ η i ≤ r := by simp [originBox, Set.mem_pi]

theorem measurableSet_originBox (d : ℕ) (r : ℝ) : MeasurableSet (originBox d r) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem volume_originBox (d : ℕ) (r : ℝ) :
    volume (originBox d r) = (ENNReal.ofReal r)^d := by
  simp [originBox, Real.volume_pi_Ioc]

def packetBump (d : ℕ) (r : ℝ) : Space d → ℂ :=
  (originBox d r).indicator (fun _ => 1)

theorem measurable_packetBump (d : ℕ) (r : ℝ) : Measurable (packetBump d r) :=
  measurable_const.indicator (measurableSet_originBox d r)

theorem packetBump_bound (d : ℕ) (r : ℝ) (ξ : Space d) : ‖packetBump d r ξ‖ ≤ 1 := by
  by_cases h : ξ ∈ originBox d r <;> simp [packetBump, h]

theorem packetBump_memLp (d : ℕ) (r : ℝ) (p : ℝ≥0∞) : MemLp (packetBump d r) p volume := by
  apply memLp_indicator_const p (measurableSet_originBox d r).nullMeasurableSet
  right
  rw [volume_originBox]
  finiteness

theorem packetBump_integrable (d : ℕ) (r : ℝ) : Integrable (packetBump d r) :=
  memLp_one_iff_integrable.mp (packetBump_memLp d r 1)

end RTS.Transference
