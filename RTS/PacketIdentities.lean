module

public import RTS.Transference

/-! # Identities for lifting the weight and thickening the data -/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace RTS.Transference

variable {d : ℕ}

/-- Extend the weight periodically in space and truncate it to one time period. -/
def liftedWeight (w : Torus d × UnitAddCircle → ℝ) (z : Space d × ℝ) : ℝ :=
  if z.2 ∈ Ioc (0 : ℝ) 1 then w (fun i => (z.1 i : UnitAddCircle), (z.2 : UnitAddCircle)) else 0

/-- At integer velocities, lifting a weight preserves its ray integral exactly.
This uses the paper's factor two and the probability normalization of Haar measure. -/
theorem integer_ray_lift (w : Torus d × UnitAddCircle → ℝ) (x : Space d) (k : Freq d) :
    eucXray (liftedWeight w) x (fun i => (k i : ℝ)) =
      perXray w (fun i => (x i : UnitAddCircle)) k := by
  let f (s : UnitAddCircle) := ENNReal.ofReal (w (fun i =>
    (x i : UnitAddCircle) - (2 * k i) • s, s))
  have h (t : ℝ) (i : Fin d) :
      (↑(x i - 2 * t * (k i : ℝ)) : UnitAddCircle) = (x i : UnitAddCircle) - (2 * k i) • (t : UnitAddCircle) := by
    rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_sub]
    congr 1
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat]
    ring
  have hi (t : ℝ) : ENNReal.ofReal (liftedWeight w (fun i => x i - 2*t*(k i : ℝ),t)) =
      (Ioc (0:ℝ) 1).indicator (fun t : ℝ => f (t : UnitAddCircle)) t := by
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [liftedWeight, ht, f, h]
  unfold eucXray perXray
  simp_rw [hi]
  rw [lintegral_indicator measurableSet_Ioc]
  calc
    _ = ∫⁻ t : UnitAddCircle, f t := by simpa using UnitAddCircle.lintegral_preimage 0 f
    _ = _ := by rw [AddCircle.volume_eq_smul_haarAddCircle]; simp [f, circleMeasure]

abbrev latticePoint (k : Freq d) : Space d := fun i => k i

/-- Translation by a lattice site produces a Fourier character in the common packet
offset. The integer–integer term in the phase is an integer multiple of (2π). -/
theorem packet_phase_translate (x η : Space d) (t : ℝ) (j k : Freq d) :
    euPhase (x + latticePoint j) (latticePoint k + η) t =
      euPhase η (latticePoint j) 0 * euPhase x (latticePoint k + η) t := by
  unfold euPhase
  let m : ℤ := ∑ i, j i * k i
  have hd : dot (x+latticePoint j) (latticePoint k+η) =
      dot x (latticePoint k+η) + dot η (latticePoint j) + (m : ℝ) := by
    unfold dot m latticePoint
    push_cast
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd, ← Complex.exp_add]
  have he := Complex.exp_int_mul_two_pi_mul_I m
  calc
    _ = Complex.exp ((m : ℂ)*(2*Real.pi*Complex.I)) *
        Complex.exp (((2*Real.pi*(dot η (latticePoint j) + 0 * dot (latticePoint j) (latticePoint j)) : ℝ) : ℂ)*Complex.I +
          ((2*Real.pi*(dot x (latticePoint k+η) + t*dot (latticePoint k+η) (latticePoint k+η)) : ℝ) : ℂ)*Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
    _ = _ := by rw [he, one_mul]

/-- Explicit frequency profile of the superposed Euclidean packets. -/
def thickenedProfile (g : Space d → ℂ) (a : Freq d →₀ ℂ) (ξ : Space d) : ℂ :=
  ∑ k ∈ a.support, a k * g (ξ-latticePoint k)

/-- The Euclidean solution at the lattice translates of a point in the unit cell,
expressed as the Fourier integral in the common frequency offset. -/
theorem physical_packet_integral (g : Space d → ℂ) (hg : Integrable g)
    (a : Freq d →₀ ℂ) (x : Space d) (t : ℝ) (j : Freq d) :
    eucWave (thickenedProfile g a) (x+latticePoint j) t =
      ∫ η, euPhase η (latticePoint j) 0 * g η * shiftedWave a (x,t) η := by
  have int_phase (b : Space d → ℂ) (hb : Integrable b) (y : Space d) (s : ℝ) :
      Integrable (fun ξ => b ξ * euPhase y ξ s) :=
    hb.mul_bdd (g := fun ξ => euPhase y ξ s) (c := 1) (Continuous.aestronglyMeasurable (by unfold euPhase dot; fun_prop))
      (ae_of_all _ fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
  have hterm (k : Freq d) : Integrable (fun ξ => a k * g (ξ-latticePoint k) *
      euPhase (x+latticePoint j) ξ t) :=
    int_phase _ ((hg.comp_sub_right _).const_mul _) _ _
  let B (k : Freq d) (η : Space d) := a k * g η *
      euPhase (x+latticePoint j) (η+latticePoint k) t
  have heq (k : Freq d) :
      (fun ξ => a k * g (ξ-latticePoint k) * euPhase (x+latticePoint j) ξ t) =
        fun ξ => B k (ξ-latticePoint k) := by
    funext ξ
    simp [B]
  have hB (k : Freq d) : Integrable (B k) := by
    have h' := (hterm k).comp_add_right (latticePoint k)
    simpa [heq] using h'
  unfold eucWave thickenedProfile
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _ => hterm k)]
  simp_rw [heq, integral_sub_right_eq_self]
  rw [← integral_finsetSum _ (fun k _ => hB k)]
  apply integral_congr_ae
  filter_upwards with η
  simp only [B, add_comm η, packet_phase_translate, shiftedWave, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring


/-- A half-open unit cell in frequency space. -/
def frequencyCell (c : Space d) : Set (Space d) :=
  {ξ | ∀ i, ξ i ∈ Ioc (c i) (c i+1)}

/-- The representative of a torus point in the chosen cell. -/
def representative (c : Space d) (z : Torus d) : Space d :=
  (UnitAddTorus.measurableEquivPiIoc c z).1

theorem representative_in_cell (c : Space d) {ξ : Space d} (hξ : ξ ∈ frequencyCell c) :
    representative c (fun i => (ξ i : UnitAddCircle)) = ξ := by
  exact congrArg Subtype.val ((UnitAddTorus.measurableEquivPiIoc c).apply_symm_apply ⟨ξ,hξ⟩)

/-- The integrand in the frequency cell, as a function on the auxiliary torus. -/
def cellPacket (c : Space d) (g : Space d → ℂ) (a : Freq d →₀ ℂ)
    (p : Space d × ℝ) (z : Torus d) : ℂ :=
  g (representative c z) * shiftedWave a p (representative c z)

/-- The physical lattice translates are Fourier coefficients on the auxiliary torus. -/
theorem physical_packet_coefficient (g : Space d → ℂ) (hg : Integrable g)
    (c : Space d) (hs : Function.support g ⊆ frequencyCell c)
    (a : Freq d →₀ ℂ) (x : Space d) (t : ℝ) (j : Freq d) :
    eucWave (thickenedProfile g a) (x+latticePoint j) t =
      UnitAddTorus.mFourierCoeff (cellPacket c g a (x,t)) (-j) := by
  rw [physical_packet_integral g hg, UnitAddTorus.mFourierCoeff_eq_integral _ _ c]
  change _ = ∫ ξ in frequencyCell c, _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := frequencyCell c) (f := fun η => euPhase η (latticePoint j) 0 * g η * shiftedWave a (x,t) η)
    (fun η hη => by simp [Function.notMem_support.mp (fun h => hη (hs h))])]
  apply setIntegral_congr_fun (MeasurableSet.univ_pi' fun _ => measurableSet_Ioc)
  intro η hη
  have he : euPhase η (latticePoint j) 0 =
      UnitAddTorus.mFourier j (fun i => (η i : UnitAddCircle)) := by
    simpa [latticePoint] using euPhase_int η 0 j
  simp only [neg_neg, cellPacket, representative_in_cell c hη, he, smul_eq_mul, mul_assoc]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The exact squared-energy Parseval identity from §3.1 for an integrable, bounded,
measurable packet supported inside one frequency cell. -/
theorem physical_packet_hasSum (g : Space d → ℂ) (hg : Integrable g) (hgm : Measurable g)
    (B : ℝ) (hb : ∀ η, ‖g η‖ ≤ B) (c : Space d) (hs : Function.support g ⊆ frequencyCell c)
    (a : Freq d →₀ ℂ) (x : Space d) (t : ℝ) :
    HasSum (fun j : Freq d => ‖eucWave (thickenedProfile g a) (x+latticePoint j) t‖ ^ 2)
      (∫ η in frequencyCell c, ‖g η‖ ^ 2 * ‖shiftedWave a (x,t) η‖ ^ 2) := by
  let G := cellPacket c g a (x,t)
  have hrep : Measurable (representative c) :=
    measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc c).measurable
  have hG : MemLp G 2 (torusMeasure d) := by
    apply MemLp.of_bound (C := B * ∑ k ∈ a.support, ‖a k‖)
    · apply Measurable.aestronglyMeasurable
      exact (hgm.comp hrep).mul (((shiftedWave_continuous a).comp
        (continuous_const.prodMk continuous_id)).measurable.comp hrep)
    · apply ae_of_all
      intro z
      change ‖_ * _‖ ≤ _
      rw [norm_mul]
      apply mul_le_mul (hb _) _ (norm_nonneg _) (le_trans (norm_nonneg (g 0)) (hb 0))
      calc
        ‖shiftedWave a (x,t) (representative c z)‖ ≤
          ∑ k ∈ a.support, ‖a k * euPhase x (latticePoint k + representative c z) t‖ :=
            norm_sum_le _ _
        _ = _ := by simp only [norm_mul, euPhase, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcoeff (j : Freq d) : UnitAddTorus.mFourierCoeff (hG.toLp G) (-j) =
      UnitAddTorus.mFourierCoeff G (-j) := by
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with z hz
    simp only [hz]
  simp_rw [physical_packet_coefficient g hg c hs a x t,
    ← show ∀ j, UnitAddTorus.mFourierCoeff (hG.toLp G) (-j) =
      UnitAddTorus.mFourierCoeff (cellPacket c g a (x,t)) (-j) from hcoeff]
  have hh := ((Equiv.neg (Freq d)).hasSum_iff.mpr (UnitAddTorus.hasSum_sq_mFourierCoeff (hG.toLp G)))
  suffices he : (∫ z, ‖(hG.toLp G) z‖ ^ 2 ∂torusMeasure d) =
      ∫ η in frequencyCell c, ‖g η‖ ^ 2 * ‖shiftedWave a (x,t) η‖ ^ 2 by
    rw [← he]
    exact hh
  calc
    _ = ∫ z, ‖G z‖ ^ 2 ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [hG.coeFn_toLp] with z hz
      rw [hz]
    _ = _ := by
      trans ∫ η in frequencyCell c, ‖G (fun i => (η i : UnitAddCircle))‖ ^ 2
      · exact UnitAddTorus.integral_preimage (fun z => ‖G z‖ ^ 2) c
      apply setIntegral_congr_fun (MeasurableSet.univ_pi' fun _ => measurableSet_Ioc)
      intro η hη
      simp [G, cellPacket, representative_in_cell c hη, mul_pow]

/-- The summed form of the pointwise Parseval identity. -/
theorem physical_packet_parseval (g : Space d → ℂ) (hg : Integrable g) (hgm : Measurable g)
    (B : ℝ) (hb : ∀ η, ‖g η‖ ≤ B) (c : Space d) (hs : Function.support g ⊆ frequencyCell c)
    (a : Freq d →₀ ℂ) (x : Space d) (t : ℝ) :
    (∑' j : Freq d, ‖eucWave (thickenedProfile g a) (x+latticePoint j) t‖ ^ 2) =
      ∫ η in frequencyCell c, ‖g η‖ ^ 2 * ‖shiftedWave a (x,t) η‖ ^ 2 := by
  exact (physical_packet_hasSum g hg hgm B hb c hs a x t).tsum_eq

end RTS.Transference
