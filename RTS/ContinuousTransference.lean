module

public import RTS.PacketRHS
public import RTS.PacketLHS

/-! # Quantitative transference for all continuous nonnegative torus weights -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace RTS.Transference

variable {d : ℕ}

private def cost (kind : EstimateKind) (a : Freq d →₀ ℂ) (X : Space d → ℝ) (r : ℝ) : ℝ≥0∞ :=
  match kind with
  | .stein => ENNReal.ofReal (steinAverage a X r)
  | .mt => (∑ k ∈ a.support, ‖a k‖ₑ ^ 2) * ENNReal.ofReal (mtEnvelope a X r)

private theorem cost_continuous (kind : EstimateKind) (a : Freq d →₀ ℂ) {X : Space d → ℝ}
    (hX : Continuous X) : Continuous (cost kind a X) := by
  cases kind with
  | stein => exact ENNReal.continuous_ofReal.comp (steinAverage_continuous a hX)
  | mt =>
    have hmass : (∑ k ∈ a.support, ‖a k‖ₑ ^ 2) ≠ ∞ :=
      (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.pow_lt_top enorm_lt_top).ne
    exact (ENNReal.continuous_const_mul hmass).comp
      (ENNReal.continuous_ofReal.comp (mtEnvelope_continuous a hX))

private theorem cost_zero_le (kind : EstimateKind) (a : Freq d →₀ ℂ)
    (w : Torus d × UnitAddCircle → ℝ) (hw : Continuous w) (h₀ : ∀ z, 0 ≤ w z) :
    cost kind a (continuousRayMax (realTimeWeight w)) 0 ≤ perRHS kind a w := by
  let X := continuousRayMax (realTimeWeight w)
  have hX : Continuous X := continuous_rayMax (realTimeWeight_continuous hw)
  have hX₀ : ∀ v, 0 ≤ X v := rayMax_nonneg h₀
  cases kind with
  | stein =>
    apply le_of_eq
    simp only [cost, steinAverage_zero, perRHS, perXray_sup_eq_continuousRayMax w hw h₀]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (hX₀ _))]
    simp only [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      X]
  | mt =>
    change (∑ k ∈ a.support, ‖a k‖ₑ^2) * ENNReal.ofReal (mtEnvelope a X 0) ≤ _
    by_cases ha : a.support.Nonempty
    · obtain ⟨k,hk,he⟩ := mtEnvelope_zero_attained a hX ha
      apply mul_le_mul_right
      rw [he]
      apply le_iSup_of_le (⟨k,hk⟩ : a.support)
      exact (perXray_sup_eq_continuousRayMax w hw h₀ _).ge
    · simp [Finset.not_nonempty_iff_eq_empty.mp ha, perRHS]

private theorem scaled_cost (kind : EstimateKind) (a : Freq d →₀ ℂ)
    (w : Torus d × UnitAddCircle → ℝ) (hw : Continuous w) (h₀ : ∀ z, 0 ≤ w z)
    {r : ℝ} (hr : 0 < r) (hr' : r < 1/2) :
    eucRHS kind (thickenedProfile (packetBump d r) a) (liftedWeight w) ≤
      ENNReal.ofReal (r^d) * cost kind a (continuousRayMax (realTimeWeight w)) r := by
  let X := continuousRayMax (realTimeWeight w)
  have hX : Continuous X := continuous_rayMax (realTimeWeight_continuous hw)
  cases kind with
  | stein =>
    rw [stein_profile_rhs hr hr' a w hw h₀, ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    rfl
  | mt =>
    simp only [eucRHS, cost, profile_mass hr' a, ENNReal.ofReal_pow hr.le, ← mul_assoc]
    apply mul_le_mul_right
    apply iSup_le
    intro v
    rw [lifted_eucXray_sup w hw h₀]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (profile_freqSupport a r v.property)
    exact cost_le_mtEnvelope a hX hr k.property hk

/-- For a single admissible finite Euclidean constant, a single torus polynomial and any
continuous nonnegative weight, transfer the inequality with exactly the same constant. -/
theorem continuous_transfer {N : ℝ} (kind : EstimateKind) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hE : eucAdmissible (d := d) kind (N+1) C)
    (a : Freq d →₀ ℂ) (ha : perInBox N a)
    (w : Torus d × UnitAddCircle → ℝ) (hw : Continuous w) (h₀ : ∀ z, 0 ≤ w z) :
    perLHS a w ≤ C * perRHS kind a w := by
  let X := continuousRayMax (realTimeWeight w)
  have hX : Continuous X := continuous_rayMax (realTimeWeight_continuous hw)
  have hle {r : ℝ} (hr : 0 < r) (hr' : r < 1/2) :
      ENNReal.ofReal (cellEnergy a w r) ≤ C * cost kind a X r := by
    let D := ENNReal.ofReal (r^d)
    have hD : D ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
    have hDt : D ≠ ∞ := ENNReal.ofReal_ne_top
    have h₁ : r ≤ 1 := by linarith
    have h0 := hE _ (profile_memLp a r) (profile_in_box a ha h₁) _ (liftedWeight_eligible w hw h₀)
    have h2 := h0.trans (mul_le_mul_right (scaled_cost kind a w hw h₀ hr hr') C)
    rw [packetLHS_cell a w hw h₀ r h₁] at h2
    change ENNReal.ofReal (∫ t in Icc (0:ℝ) 1, ∫ x in unitBox d, (∫ η in originBox d r,
        ‖shiftedWave a (x,t) η‖^2) * weightValue w (x,t)) ≤ _ at h2
    rw [integral_packet_energy a w r hr, ENNReal.ofReal_mul (pow_nonneg hr.le _), mul_left_comm C] at h2
    change D * ENNReal.ofReal (cellEnergy a w r) ≤ D * (C * cost kind a X r) at h2
    have := mul_le_mul_right h2 D⁻¹
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hD hDt, one_mul] using this
  have hlim : ENNReal.ofReal (cellEnergy a w 0) ≤ C * cost kind a X 0 := by
    apply le_of_tendsto_of_tendsto (b := 𝓝[>] (0:ℝ))
      ((ENNReal.continuous_ofReal.comp (cellEnergy_continuous a hw)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
      (((ENNReal.continuous_const_mul hC).comp (cost_continuous kind a hX)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1/2)] with r hr using hle hr.1 hr.2
  apply le_trans _ (mul_le_mul_right (cost_zero_le kind a w hw h₀) C)
  rw [perLHS_cell a w hw h₀]
  simpa only [cellEnergy, boxAverage_zero, weightValue, weighOnCell, unitBox] using hlim

end RTS.Transference
