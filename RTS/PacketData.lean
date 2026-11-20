module

public import RTS.PacketBox
public import RTS.PacketIdentities

/-! Frequency-side localization and integration of the explicit packets for §3.1. -/
@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace RTS.Transference

variable {d : ℕ}

theorem packetBump_cell {r : ℝ} (hr : r ≤ 1) :
    Function.support (packetBump d r) ⊆ frequencyCell 0 := by
  intro ξ hξ i
  have hm : ξ ∈ originBox d r := Set.support_indicator_subset hξ
  simpa only [Pi.zero_apply, zero_add] using
    ⟨(mem_originBox.mp hm i).1, (mem_originBox.mp hm i).2.trans hr⟩

theorem profile_memLp (a : Freq d →₀ ℂ) (r : ℝ) :
    MemLp (thickenedProfile (packetBump d r) a) 2 volume := by
  unfold thickenedProfile
  exact memLp_finsetSum _ fun k _ =>
    ((packetBump_memLp d r 2).comp_measurePreserving (measurePreserving_sub_right volume
      (latticePoint k))).const_mul _

/-- The finite union of the closed translated packet boxes, including their faces. -/
def closedPackets (a : Freq d →₀ ℂ) (r : ℝ) : Set (Space d) :=
  ⋃ k : ↥a.support, {ξ | ∀ i, ξ i - ((k : Freq d) i : ℝ) ∈ Icc 0 r}

theorem isClosed_closedPackets (a : Freq d →₀ ℂ) (r : ℝ) : IsClosed (closedPackets a r) := by
  unfold closedPackets
  apply isClosed_iUnion_of_finite
  intro k
  rw [show {ξ : Space d | ∀ i, ξ i - ((k : Freq d) i : ℝ) ∈ Icc 0 r} =
    ⋂ i, (fun ξ : Space d => ξ i - ((k : Freq d) i : ℝ)) ⁻¹' Icc 0 r by ext; simp]
  exact isClosed_iInter fun i => isClosed_Icc.preimage ((continuous_apply i).sub continuous_const)

theorem profile_freqSupport (a : Freq d →₀ ℂ) (r : ℝ) :
    freqSupport (thickenedProfile (packetBump d r) a) ⊆ closedPackets a r := by
  have hc := isClosed_closedPackets a r
  apply Measure.support_subset_of_isClosed hc
  change (volume.withDensity (fun ξ => ‖thickenedProfile (packetBump d r) a ξ‖ₑ ^ 2))
    (closedPackets a r)ᶜ = 0
  rw [withDensity_apply _ hc.measurableSet.compl]
  calc
    _ = ∫⁻ _ξ in (closedPackets a r)ᶜ, (0 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun hc.measurableSet.compl
      intro ξ hξ
      have hz : thickenedProfile (packetBump d r) a ξ = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hnot : ξ - latticePoint k ∉ originBox d r := by
          intro h
          apply hξ
          exact mem_iUnion.mpr ⟨⟨k,hk⟩, fun i => ⟨(mem_originBox.mp h i).1.le, (mem_originBox.mp h i).2⟩⟩
        simp [packetBump, hnot]
      simp [hz]
    _ = _ := by simp

theorem profile_in_box {N r : ℝ} (a : Freq d →₀ ℂ) (ha : perInBox N a) (hr : r ≤ 1) :
    ∀ v ∈ freqSupport (thickenedProfile (packetBump d r) a), inBox (N+1) v := by
  intro v hv i
  obtain ⟨k,hk⟩ := mem_iUnion.mp (profile_freqSupport a r hv)
  have h₁ := hk i
  have h₂ := abs_le.mp (ha k k.property i)
  exact abs_le.mpr ⟨by linarith [h₁.1], by linarith [h₁.2]⟩

/-- Squared Fourier modulus is the sum of the squared moduli on disjoint packets. -/
theorem profile_enorm_sq {r : ℝ} (hr : r < 1/2) (a : Freq d →₀ ℂ) (ξ : Space d) :
    ‖thickenedProfile (packetBump d r) a ξ‖ₑ ^ 2 =
      ∑ k ∈ a.support, ‖a k‖ₑ ^ 2 * ‖packetBump d r (ξ - latticePoint k)‖ₑ ^ 2 := by
  have hs (k : Freq d) : Function.support (fun z => packetBump d r (z - latticePoint k)) ⊆ packetCube k (1/2) := by
    intro z hz i
    have h : z - latticePoint k ∈ originBox d r := Set.support_indicator_subset hz
    have hi := mem_originBox.mp h i
    change |(z - latticePoint k) i| < 1/2
    rw [abs_of_pos hi.1]
    exact hi.2.trans_lt hr
  have he := norm_sq_packet_sum a.support a (fun k z => packetBump d r (z - latticePoint k))
    le_rfl (fun k _ => hs k) ξ
  have h := congrArg ENNReal.ofReal he
  simpa only [thickenedProfile, ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

/-- Exact translated integrals on the frequency packets, weighted by any nonnegative
measurable function of the velocity. The constant function one gives the mass identity. -/
theorem profile_integral {r : ℝ} (hr : r < 1/2) (a : Freq d →₀ ℂ)
    (H : Space d → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ξ, ‖thickenedProfile (packetBump d r) a ξ‖ₑ ^ 2 * H ξ) =
      ∑ k ∈ a.support, ‖a k‖ₑ ^ 2 * ∫⁻ η in originBox d r, H (latticePoint k + η) := by
  simp_rw [profile_enorm_sq hr, Finset.sum_mul, mul_assoc]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [lintegral_const_mul' _ _ (by finiteness)]
    congr 1
    let f (ξ : Space d) := ‖packetBump d r (ξ - latticePoint k)‖ₑ^2 * H ξ
    rw [← lintegral_add_left_eq_self f (latticePoint k)]
    calc
      _ = ∫⁻ η, (originBox d r).indicator (fun η => H (latticePoint k + η)) η := by
        apply lintegral_congr
        intro η
        dsimp only [f]
        by_cases z : η ∈ originBox d r <;> simp [packetBump, add_sub_cancel_left, z]
      _ = _ := lintegral_indicator (measurableSet_originBox d r) _
  · intro k _
    exact measurable_const.mul ((((measurable_packetBump d r).comp (measurable_sub_const _)).enorm.pow_const _).mul hH)

end RTS.Transference
