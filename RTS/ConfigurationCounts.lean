module

public import RTS.Configuration
public import RTS.ConfigurationFourier
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Fin.Tuple.Reflection

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators

namespace RTS.Configuration

abbrev q (a : Point) : ℤ := ∑ i, a i ^ 2

/-- Under the parallelogram equation, equality of energies says that adjacent sides
are perpendicular. The equivalence also holds for coincident vertices. -/
theorem rectangle_resonance (a b c e : Point) :
    (a + c = b + e ∧ q a + q c = q b + q e) ↔ IsRectangle a b c e := by
  unfold IsRectangle
  refine and_congr_right fun h => ?_
  have hc : c = b + e - a := by rw [← h]; abel
  subst c
  simp only [q, dot₂, Fin.sum_univ_two, Pi.sub_apply, Pi.add_apply]
  constructor <;> intro h
  · linarith only [show
        a 0 ^ 2 + a 1 ^ 2 + ((b 0 + e 0 - a 0)^2 + (b 1 + e 1 - a 1)^2) -
          ((b 0 ^ 2 + b 1 ^ 2) + (e 0 ^ 2 + e 1 ^ 2)) =
          2 * ((b 0-a 0)*(e 0-a 0) + (b 1-a 1)*(e 1-a 1)) by ring, h]
  · linear_combination 2*h

private theorem fourth_power_pair (A : Finset Point) (x : Torus 2) (t : UnitAddCircle) :
    ‖configWave A x t‖ ^ 4 =
    ‖∑ p ∈ A ×ˢ A, atom (p.1 + p.2) (q p.1 + q p.2) x t‖ ^ 2 := by
  have hf : (configWave A x t)^2 = ∑ p ∈ A ×ˢ A, atom (p.1 + p.2) (q p.1 + q p.2) x t := by
    unfold configWave
    rw [sq, Finset.sum_product, Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => atom_mul i j _ _ x t
  rw [← hf, norm_pow]
  ring

theorem rectangle_integral (A : Finset Point) :
    (∫ t, ∫ x, ‖configWave A x t‖ ^ 4 ∂torusMeasure 2 ∂circleMeasure) = rectangleCount A := by
  classical
  let S := A ×ˢ A
  have hh := atom_energy S (fun p => p.1 + p.2) (fun p => q p.1 + q p.2)
  dsimp only [S] at hh
  simp_rw [← fourth_power_pair A, integral_complex_ofReal] at hh
  have hr := congrArg Complex.re hh
  simp only [Complex.ofReal_re, Complex.natCast_re] at hr
  rw [hr]
  norm_cast
  unfold rectangleCount
  change ((S ×ˢ S).filter _).card = _
  simp_rw [Finset.card_filter, S, Finset.sum_product]
  simp only [rectangle_resonance, IsRectangle]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

abbrev rayEnergy (a k : Point) : ℤ := q a - 2 * dot₂ a k

/-- A Fourier pair survives integration along the ray with velocity 2k exactly when
it is an ordered isosceles triangle with apex k. -/
theorem triangle_resonance (a b k : Point) :
    rayEnergy a k = rayEnergy b k ↔ IsTriangle a b k := by
  simp only [rayEnergy, q, dot₂, IsTriangle, Fin.sum_univ_two, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.ofNat_apply, Nat.cast_ofNat]
  constructor <;> intro h <;> linear_combination h

private theorem ray_character (m l : ℤ) (y t : UnitAddCircle) :
    fourier m (y - l • t) = fourier m y * fourier (-(m*l)) t := by
  simp only [fourier_apply, sub_eq_add_neg, smul_add, smul_neg, smul_smul, neg_smul,
    AddCircle.toCircle_add, Circle.coe_mul]

private theorem ray_atom (a k : Point) (x : Torus 2) (t : UnitAddCircle) :
    atom a (q a) (fun i => x i - (2 * k i) • t) t =
    UnitAddTorus.mFourier a x * fourier (rayEnergy a k) t := by
  simp only [atom, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    ray_character, rayEnergy, dot₂, Fin.sum_univ_two]
  have he : q a - 2 * (a 0 * k 0 + a 1 * k 1) =
      -(a 0 * (2 * k 0)) + -(a 1 * (2 * k 1)) + q a := by ring
  simp only [q, Fin.sum_univ_two] at he
  rw [he]
  simp only [fourier_add]
  ring

/-- Weighted, one-dimensional finite Parseval with multiple indices allowed at the
same frequency. -/
theorem circle_energy {ι : Type*} (S : Finset ι) (v : ι → ℂ) (h : ι → ℤ) :
    (∫ t : UnitAddCircle, ((‖∑ i ∈ S, v i * fourier (h i) t‖ ^ 2 : ℝ) : ℂ) ∂circleMeasure) =
    ∑ p ∈ (S ×ˢ S).filter (fun p => h p.1 = h p.2), v p.1 * conj (v p.2) := by
  classical
  have expan (t : UnitAddCircle) :
      ((‖∑ i ∈ S, v i * fourier (h i) t‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ S ×ˢ S, (v p.1 * conj (v p.2)) * (fourier (h p.1) t * conj (fourier (h p.2) t)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_product, Finset.sum_mul]
    simp only [Finset.mul_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [expan]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, circle_orthogonality]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp
  · intro p _
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)

private theorem ray_energy_integral (A : Finset Point) (x : Torus 2) (k : Point) :
    ((∫ t, ‖configWave A (fun i => x i - (2 * k i) • t) t‖ ^ 2 ∂circleMeasure : ℝ) : ℂ) =
      ∑ p ∈ (A ×ˢ A).filter (fun p => rayEnergy p.1 k = rayEnergy p.2 k),
      UnitAddTorus.mFourier p.1 x * conj (UnitAddTorus.mFourier p.2 x) := by
  rw [← integral_complex_ofReal]
  change (∫ t, ((‖∑ a ∈ A, atom a (q a) (fun i => x i - (2 * k i) • t) t‖ ^ 2 : ℝ) : ℂ) ∂circleMeasure) = _
  simp_rw [ray_atom]
  exact circle_energy A (fun a => UnitAddTorus.mFourier a x) (rayEnergy · k)

theorem pinned_integral_le (A : Finset Point) (x : Torus 2) (k : Point) :
    (∫ t, ‖configWave A (fun i => x i - (2 * k i) • t) t‖ ^ 2 ∂circleMeasure) ≤
      pinnedTriangleCount A k := by
  classical
  let S := (A ×ˢ A).filter fun p => rayEnergy p.1 k = rayEnergy p.2 k
  have hn : ∀ a : Point, ‖UnitAddTorus.mFourier a x‖ = 1 := by
    intro a
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
      Circle.norm_coe, Finset.prod_const_one]
  have bound := norm_sum_le S (fun p => UnitAddTorus.mFourier p.1 x * conj (UnitAddTorus.mFourier p.2 x))
  change ‖_‖ ≤ _ at bound
  rw [← ray_energy_integral] at bound
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_conj, hn,
    Finset.sum_const, nsmul_eq_mul, mul_one] at bound
  have hcard : S.card = pinnedTriangleCount A k := by
    simp only [S, pinnedTriangleCount, Finset.card_filter, Finset.sum_product,
      triangle_resonance, IsTriangle]
  exact (le_abs_self _).trans (by simpa only [hcard] using bound)

/-- Equality in the pinned estimate is attained at the spatial origin. -/
theorem pinned_integral_at_zero (A : Finset Point) (k : Point) :
    (∫ t, ‖configWave A (fun i => 0 - (2 * k i) • t) t‖ ^ 2 ∂circleMeasure) =
      pinnedTriangleCount A k := by
  classical
  have hh := ray_energy_integral A (0 : Torus 2) k
  have he (a : Point) : UnitAddTorus.mFourier a (0 : Torus 2) = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.zero_apply,
      fourier_eval_zero, Finset.prod_const_one]
  have hcard : ((A ×ˢ A).filter (fun p => rayEnergy p.1 k = rayEnergy p.2 k)).card =
      pinnedTriangleCount A k := by
    simp only [pinnedTriangleCount, Finset.card_filter, Finset.sum_product,
      triangle_resonance, IsTriangle]
  simpa only [he, map_one, mul_one, Finset.sum_const, nsmul_eq_mul,
    Pi.zero_apply, Complex.ofReal_re, Complex.natCast_re, hcard] using congrArg Complex.re hh

end RTS.Configuration
