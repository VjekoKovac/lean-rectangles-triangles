module

public import RTS.LiftingAssembly
public import RTS.LiftingRectLower
public import RTS.LiftingPinnedUpper
public import RTS.GeometricLift

/-! The quantitative fixed-modulus bound from Proposition 2.1, in the form
needed simultaneously for box radius and exact cardinality. -/
@[expose] public noncomputable section
namespace RTS
open Real CRT Lifting

/-- At every radius above exp(1000 q²) the common coefficient in UniformLiftBounds
cancels, leaving the factor (4/3)^|P| and only absolute losses. -/
theorem fixed_modulus_bound (P : PrimeSet) :
    UniformLiftBounds (circleLift P.modulus) 1000
      (((1/1024 : ℝ)/2)/(9*(10000+1)) * (4/3:ℝ)^P.primes.card) P.modulus := by
  apply uniformLiftBounds_of_tuples P (c := 1/1024) (D := 10000) (C := 1000)
    (by norm_num) (by norm_num) (by norm_num)
  · intro N hN
    calc
      _ = P.rects.card * ((N:ℝ)^4 * log N / (1024*(P.modulus:ℝ)^6)) := by
        unfold liftScale
        ring
      _ ≤ _ := rectTupleSet_lower P.modulus_pos P.rects P.admissible_rectangle_residue hN
  · intro N hN b
    calc
      _ ≤ _ := pinTupleSet_upper_threshold P.modulus_pos (P.pins b) hN
      _ = _ := by unfold pinScale; ring
  · exact rect_tuple_count_le P
  · exact fun _ _ hk => pin_count_le_tuples P hk

end RTS
