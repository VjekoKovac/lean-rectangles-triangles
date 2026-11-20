module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

/-! Finite character orthogonality for the counting argument of Section 4. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate BigOperators

namespace RTS.Configuration

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : ℕ}
abbrev SpatialMeasure (d : ℕ) : Measure (UnitAddTorus (Fin d)) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

/-- Orthogonality, with the probability normalization of mathlib's Fourier basis. -/
theorem circle_orthogonality (m n : ℤ) :
    (∫ t : UnitAddCircle, fourier m t * conj (fourier n t) ∂AddCircle.haarAddCircle) =
    if m = n then 1 else 0 := by
  simpa only [ContinuousMap.inner_toLp, eq_comm] using
    (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1 : ℝ))) n m)

/-- The multidimensional counterpart, with product probability measure. -/
theorem torus_orthogonality (m n : Fin d → ℤ) :
    (∫ x, UnitAddTorus.mFourier m x * conj (UnitAddTorus.mFourier n x) ∂SpatialMeasure d) =
    if m = n then 1 else 0 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, map_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun i t => fourier (m i) t * conj (fourier (n i) t))]
  simp_rw [circle_orthogonality]
  by_cases he : m = n
  · simp [he]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    simp only [he, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

abbrev atom (k : Fin d → ℤ) (h : ℤ) (x : UnitAddTorus (Fin d)) (t : UnitAddCircle) : ℂ :=
  UnitAddTorus.mFourier k x * fourier h t

theorem atom_mul (k l : Fin d → ℤ) (h j : ℤ) (x : UnitAddTorus (Fin d)) (t : UnitAddCircle) :
    atom k h x t * atom l j x t = atom (k+l) (h+j) x t := by
  simp only [atom, UnitAddTorus.mFourier_add, fourier_add]
  ring

/-- Average of a spacetime character times a conjugate. -/
theorem atom_orthogonality (k l : Fin d → ℤ) (h j : ℤ) :
    (∫ t : UnitAddCircle, ∫ x, atom k h x t * conj (atom l j x t)
        ∂SpatialMeasure d ∂AddCircle.haarAddCircle) =
      if k = l ∧ h = j then 1 else 0 := by
  have hsplit (x : UnitAddTorus (Fin d)) (t : UnitAddCircle) :
      atom k h x t * conj (atom l j x t) =
      (UnitAddTorus.mFourier k x * conj (UnitAddTorus.mFourier l x)) *
      (fourier h t * conj (fourier j t)) := by
    simp only [atom, map_mul]; ring
  simp_rw [hsplit, integral_mul_const, torus_orthogonality, integral_const_mul, circle_orthogonality]
  split_ifs <;> simp_all

private theorem sum_conj_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ S, f i) * conj (∑ i ∈ S, f i) =
      ∑ p ∈ S ×ˢ S, f p.1 * conj (f p.2) := by
  rw [map_sum, Finset.sum_product]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- Parseval for a finite list of spacetime characters, allowing repeated frequencies. -/
theorem atom_energy {ι : Type*} (S : Finset ι) (k : ι → Fin d → ℤ) (h : ι → ℤ) :
    (∫ t : UnitAddCircle, ∫ x, ((‖∑ i ∈ S, atom (k i) (h i) x t‖ ^ 2 : ℝ) : ℂ)
        ∂SpatialMeasure d ∂AddCircle.haarAddCircle) =
      (((S ×ˢ S).filter (fun p => k p.1 = k p.2 ∧ h p.1 = h p.2)).card : ℂ) := by
  classical
  simp_rw [Complex.ofReal_pow, ← Complex.mul_conj', sum_conj_sum]
  have inner (t : UnitAddCircle) : ∀ p ∈ S ×ˢ S, Integrable
      (fun x => atom (k p.1) (h p.1) x t * conj (atom (k p.2) (h p.2) x t)) (SpatialMeasure d) :=
    fun p _ => Continuous.integrable_of_hasCompactSupport (by unfold atom; fun_prop)
      (HasCompactSupport.of_compactSpace _)
  have outer : ∀ p ∈ S ×ˢ S, Integrable (fun t : UnitAddCircle => ∫ x,
      atom (k p.1) (h p.1) x t * conj (atom (k p.2) (h p.2) x t) ∂SpatialMeasure d)
      AddCircle.haarAddCircle := by
    intro p _
    have hf (x : UnitAddTorus (Fin d)) (t : UnitAddCircle) :
        atom (k p.1) (h p.1) x t * conj (atom (k p.2) (h p.2) x t) =
        (UnitAddTorus.mFourier (k p.1) x * conj (UnitAddTorus.mFourier (k p.2) x)) *
        (fourier (h p.1) t * conj (fourier (h p.2) t)) := by simp only [atom, map_mul]; ring
    simp_rw [hf, integral_mul_const]
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  simp_rw [integral_finsetSum _ (inner _)]
  rw [integral_finsetSum _ outer]
  simp_rw [atom_orthogonality]
  simp [Finset.sum_boole]

end RTS.Configuration
