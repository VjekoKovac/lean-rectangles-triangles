module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

/-!
# Thickening lattice frequencies

Auxiliary facts for §3.1 of Bennett–Kovač–Nakamura–Oliveira. The velocity and
frequency spaces use coordinates, so the frequency localization is a cube.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace RTS.Transference

variable {d : ℕ}

/-- A small open coordinate cube surrounding an integer frequency. -/
def packetCube (k : Fin d → ℤ) (r : ℝ) : Set (Fin d → ℝ) :=
  {ξ | ∀ i, |ξ i - (k i : ℝ)| < r}

/-- A radius of at most one half prevents different lattice packets from overlapping. -/
theorem packetCube_disjoint {k l : Fin d → ℤ} (hkl : k ≠ l) {r : ℝ} (hr : r ≤ 1/2) :
    Disjoint (packetCube k r) (packetCube l r) := by
  rw [Set.disjoint_left]
  intro ξ hk hl
  apply hkl
  funext i
  have h₁ := abs_lt.mp (hk i)
  have h₂ := abs_lt.mp (hl i)
  have hlower : (l i : ℝ) - 1 < k i := by linarith
  have hupper : (k i : ℝ) < (l i : ℝ) + 1 := by linarith
  have hi : l i - 1 < k i := by exact_mod_cast hlower
  have hj : k i < l i + 1 := by exact_mod_cast hupper
  omega

/-- Every thickened packet lies in the `N+1` frequency cube from Theorem 1.3. -/
theorem packetCube_subset {k : Fin d → ℤ} {N r : ℝ}
    (hk : ∀ i, |(k i : ℝ)| ≤ N) (hr : r ≤ 1) :
    packetCube k r ⊆ {ξ | ∀ i, |ξ i| ≤ N+1} := by
  intro ξ hξ i
  calc |ξ i| = |ξ i - k i + k i| := by rw [sub_add_cancel]
       _ ≤ |ξ i - k i| + |(k i : ℝ)| := abs_add_le _ _
       _ ≤ N + 1 := by have hi := hξ i; have := hk i; linarith

/-- Vanishing cross terms for a finite superposition on the disjoint packets.
Applying this pointwise gives the frequency-side squared mass used in both estimates. -/
theorem norm_sq_packet_sum (A : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) (g : (Fin d → ℤ) → (Fin d → ℝ) → ℂ)
    {r : ℝ} (hr : r ≤ 1/2) (hg : ∀ k ∈ A, Function.support (g k) ⊆ packetCube k r)
    (ξ : Fin d → ℝ) :
    ‖∑ k ∈ A, a k * g k ξ‖ ^ 2 = ∑ k ∈ A, ‖a k‖ ^ 2 * ‖g k ξ‖ ^ 2 := by
  classical
  by_cases hx : ∃ k ∈ A, g k ξ ≠ 0
  · obtain ⟨k, hk, hξ⟩ := hx
    have hzero (j : Fin d → ℤ) (hj : j ∈ A) (hjk : j ≠ k) : g j ξ = 0 := by
      by_contra h
      exact (Set.disjoint_left.mp (packetCube_disjoint hjk hr)) (hg j hj h) (hg k hk hξ)
    rw [Finset.sum_eq_single_of_mem k hk (fun j hj hjk => by simp [hzero j hj hjk]),
      Finset.sum_eq_single_of_mem k hk (fun j hj hjk => by simp [hzero j hj hjk])]
    rw [norm_mul, mul_pow]
  · push Not at hx
    rw [Finset.sum_eq_zero (fun k hk => by rw [hx k hk, mul_zero]),
      Finset.sum_eq_zero (fun k hk => by simp [hx k hk])]
    simp

/-- The continuous-weight X-ray maximum on the compact torus. The velocity
is allowed to vary continuously when the frequency packets are thickened. -/
noncomputable def continuousRayMax (w : (Fin d → UnitAddCircle) × ℝ → ℝ) (v : Fin d → ℝ) : ℝ :=
  sSup ((fun x : Fin d → UnitAddCircle =>
    ∫ t in Icc (0:ℝ) 1, w (fun i => x i - (↑(2*t*v i) : UnitAddCircle), t)) '' univ)

/-- Continuity in velocity after maximizing over every spatial base point, for
continuous weights. This is the continuity input to both velocity-side limits. -/
theorem continuous_rayMax {w : (Fin d → UnitAddCircle) × ℝ → ℝ} (hw : Continuous w) :
    Continuous (continuousRayMax w) := by
  apply isCompact_univ.continuous_sSup
  apply continuous_parametric_integral_of_continuous (s := Icc (0 : ℝ) 1) _ isCompact_Icc
  apply hw.comp
  apply Continuous.prodMk _ (by fun_prop)
  apply continuous_pi
  intro i
  apply Continuous.sub (by fun_prop)
  apply (AddCircle.continuous_mk' (1 : ℝ)).comp
  fun_prop

/-- Every compactly supported frequency probability packet samples a continuous
function at its center in the limit.  The fixed probability space supplies the
undilated displacement, which can have an arbitrary continuous profile. -/
theorem integral_shrinking_packet {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (y : Y → (Fin d → ℝ)) (hy : Continuous y)
    (k : Fin d → ℝ) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    Tendsto (fun r : ℝ => ∫ z, f (k + r • y z) ∂μ) (𝓝 0) (𝓝 (f k)) := by
  have hcont : Continuous (fun r : ℝ => ∫ z in (univ : Set Y), f (k + r • y z) ∂μ) := by
    apply continuous_parametric_integral_of_continuous _ isCompact_univ
    fun_prop
  simpa using hcont.tendsto 0

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- Parseval in the sign convention of the periodized packet identity. The
physical translate indexed by `j` is the Fourier coefficient indexed by `-j`. -/
theorem sum_sq_negative_fourier_coeff
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) :
    (∑' j : Fin d → ℤ, ‖UnitAddTorus.mFourierCoeff f (-j)‖ ^ 2) = ∫ t, ‖f t‖ ^ 2 := by
  exact ((Equiv.neg (Fin d → ℤ)).tsum_eq
    (fun j => ‖UnitAddTorus.mFourierCoeff f j‖ ^ 2)).trans
    (UnitAddTorus.hasSum_sq_mFourierCoeff f).tsum_eq

end RTS.Transference
