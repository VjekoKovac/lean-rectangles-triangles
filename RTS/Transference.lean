module

public import RTS.AnalysisDefs
public import RTS.TransferencePackets

/-! # Quantitative transference from Euclidean space to the torus -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace RTS.Transference

variable {d : ℕ}

/-- The finite periodic character at an integral frequency, evaluated on real representatives,
is the Euclidean Schrödinger phase at that frequency. -/
theorem euPhase_int (x : Space d) (t : ℝ) (k : Freq d) :
    euPhase x (fun i => (k i : ℝ)) t =
    UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle)) *
      fourier (∑ i, k i ^ 2) (t : UnitAddCircle) := by
  simp only [euPhase, dot, UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [mul_add, add_mul, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

/-- The polynomial on the torus agrees exactly with the restriction of the sum of
Euclidean phases. This identifies the unthickened limit with the paper's solution. -/
theorem sum_phase_eq_perWave (a : Freq d →₀ ℂ) (x : Space d) (t : ℝ) :
    (∑ k ∈ a.support, a k * euPhase x (fun i => (k i : ℝ)) t) =
      perWave a (fun i => (x i : UnitAddCircle)) (t : UnitAddCircle) := by
  simp only [euPhase_int, perWave, mul_assoc]

/-- The common frequency shift inside the unit-cell Parseval integral in §3.1. -/
def shiftedWave (a : Freq d →₀ ℂ) (p : Space d × ℝ) (η : Space d) : ℂ :=
  ∑ k ∈ a.support, a k * euPhase p.1 ((fun i => (k i : ℝ)) + η) p.2

theorem shiftedWave_zero (a : Freq d →₀ ℂ) (p : Space d × ℝ) :
    shiftedWave a p 0 = perWave a (fun i => (p.1 i : UnitAddCircle)) (p.2 : UnitAddCircle) := by
  simpa only [shiftedWave, add_zero] using sum_phase_eq_perWave a p.1 p.2

theorem shiftedWave_continuous (a : Freq d →₀ ℂ) :
    Continuous (fun q : (Space d × ℝ) × Space d => shiftedWave a q.1 q.2) := by
  unfold shiftedWave euPhase dot
  fun_prop

/-- The integrated left-hand limit after the paper's Parseval step. Here `ν` may
already include the nonnegative weight on the unit spacetime cell `K`. The
fixed probability parameter `μ` describes the undilated frequency packet. -/
theorem weighted_packet_limit {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (y : Y → Space d) (hy : Continuous y)
    (ν : Measure (Space d × ℝ)) [IsLocallyFiniteMeasure ν]
    (K : Set (Space d × ℝ)) (hK : IsCompact K) (a : Freq d →₀ ℂ) :
    Tendsto (fun r : ℝ => ∫ p in K, ∫ z, ‖shiftedWave a p (r • y z)‖ ^ 2 ∂μ ∂ν)
      (𝓝 0) (𝓝 (∫ p in K, ‖perWave a (fun i => (p.1 i : UnitAddCircle))
        (p.2 : UnitAddCircle)‖ ^ 2 ∂ν)) := by
  have hc : Continuous (fun q : ℝ × (Space d × ℝ) =>
      ∫ z in (univ : Set Y), ‖shiftedWave a q.2 (q.1 • y z)‖ ^ 2 ∂μ) := by
    apply continuous_parametric_integral_of_continuous _ isCompact_univ
    change Continuous (fun q : (ℝ × (Space d × ℝ)) × Y =>
      ‖shiftedWave a q.1.2 (q.1.1 • y q.2)‖ ^ 2)
    have hp : Continuous (fun q : (ℝ × (Space d × ℝ)) × Y =>
      (q.1.2, q.1.1 • y q.2)) :=
      (continuous_snd.comp continuous_fst).prodMk
        ((continuous_fst.comp continuous_fst).smul (hy.comp continuous_snd))
    exact ((shiftedWave_continuous a).comp hp).norm.pow 2
  have ho : Continuous (fun r : ℝ =>
      ∫ p in K, ∫ z in (univ : Set Y), ‖shiftedWave a p (r • y z)‖ ^ 2 ∂μ ∂ν) :=
    continuous_parametric_integral_of_continuous hc hK
  simpa [shiftedWave_zero] using ho.tendsto 0

/-- The velocity-side limit for the Stein estimate. Each translated packet
samples the continuous ray maximum at its own center, then the samples are
weighted by the squared Fourier coefficients. -/
theorem stein_packet_limit {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (y : Y → Space d) (hy : Continuous y)
    (w : Torus d × ℝ → ℝ) (hw : Continuous w) (a : Freq d →₀ ℂ) :
    Tendsto (fun r : ℝ => ∑ k ∈ a.support, ‖a k‖ ^ 2 *
      ∫ z, continuousRayMax w ((fun i => (k i : ℝ)) + r • y z) ∂μ) (𝓝 0)
      (𝓝 (∑ k ∈ a.support, ‖a k‖ ^ 2 * continuousRayMax w (fun i => (k i : ℝ)))) := by
  exact tendsto_finsetSum _ fun k _ => tendsto_const_nhds.mul
    (integral_shrinking_packet μ y hy _ (continuous_rayMax hw))

/-- A simultaneous maximum over all thickened packets converges to the maximum
over unthickened frequencies, as in the MT part of §3.1. -/
theorem mt_packet_limit {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [Nonempty Y]
    (y : Y → Space d) (hy : Continuous y) (w : Torus d × ℝ → ℝ) (hw : Continuous w)
    (A : Finset (Freq d)) :
    Tendsto (fun r : ℝ => sSup ((fun p : A × Y =>
      continuousRayMax w ((fun i => ((p.1 : Freq d) i : ℝ)) + r • y p.2)) '' univ))
      (𝓝 0) (𝓝 (sSup ((fun k : A =>
        continuousRayMax w (fun i => ((k : Freq d) i : ℝ))) '' univ))) := by
  let f (r : ℝ) (p : A × Y) :=
    continuousRayMax w ((fun i => ((p.1 : Freq d) i : ℝ)) + r • y p.2)
  have hk : Continuous (fun k : A => (fun i => ((k : Freq d) i : ℝ)) : A → Space d) :=
    continuous_of_discreteTopology
  have hc : Continuous f.uncurry := by
    apply (continuous_rayMax hw).comp
    exact (hk.comp (by fun_prop)).add (by fun_prop)
  have h := (isCompact_univ.continuous_sSup (f := f) hc).tendsto 0
  convert h using 2
  congr 2
  ext z
  simp [f, Set.mem_range]
  
/-- Passing to the infimum keeps the constant one and the enlargement `N+1`. -/
theorem best_le_of_transfer (kind : EstimateKind) (N : ℝ)
    (h : ∀ C, eucAdmissible (d := d) kind (N+1) C →
      perAdmissible kind (perInBox (d := d) N) C) :
    perBest (d := d) kind (perInBox N) ≤ eucBest d kind (N+1) :=
  sInf_le_sInf fun C hC => h C hC

end RTS.Transference
