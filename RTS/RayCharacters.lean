module

public import RTS.ConfigurationFourier
public import RTS.AnalysisDefs

/-! Evaluation of a spacetime character on a Schrödinger ray in any dimension. -/
@[expose] public section

namespace RTS.Dyadic
open Configuration
open scoped BigOperators

private theorem character_translate (n b : ℤ) (x t : UnitAddCircle) :
    fourier n (x - b • t) = fourier n x * fourier (-(b*n)) t := by
  simp only [fourier_apply, sub_eq_add_neg, smul_add, smul_neg, smul_smul, neg_smul,
    AddCircle.toCircle_add, Circle.coe_mul, mul_comm n b]

private theorem fourier_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (t : UnitAddCircle) : fourier (∑ i ∈ s, f i) t = ∏ i ∈ s, fourier (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, fourier_add, ih]

theorem atom_on_ray {d : ℕ} (v k : Freq d) (h : ℤ) (x : Torus d) (t : UnitAddCircle) :
    atom v h (fun i => x i - (2*k i) • t) t =
      UnitAddTorus.mFourier v x * fourier (h - ∑ i, 2 * k i * v i) t := by
  simp only [atom, UnitAddTorus.mFourier, ContinuousMap.coe_mk, character_translate,
    Finset.prod_mul_distrib]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, fourier_add, fourier_finsetSum]
  ring

end RTS.Dyadic
