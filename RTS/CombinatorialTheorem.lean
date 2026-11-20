module

public import RTS.PrimeProducts
public import RTS.LiftingInterpolation
public import RTS.FixedModulus

/-! Theorem 1.2. Select the prime set for the desired growth rate and use the
uniform rectangle and triangle bounds at this modulus. -/
@[expose] public section

namespace RTS

open Real

theorem combinatorialGrowth : CombinatorialGrowth := by
  obtain ⟨D,hD,hprime⟩ := exists_prime_product_bound
  apply growth_of_lift_bounds (C := 1000) (a := ((1/1024 : ℝ)/2)/(9*(10000+1)))
    (D := D) (by norm_num) (by norm_num) hD
  intro m hm
  obtain ⟨P,hcard,hres,hprod⟩ := hprime m hm
  let S : CRT.PrimeSet := ⟨P,fun p hp => (hres p hp).1,fun p hp => (hres p hp).2⟩
  have hmod : S.modulus = ∏ p ∈ P, p := by
    change (∏ p : ↥P, (p : ℕ)) = _
    exact Finset.prod_attach P id
  refine ⟨S.modulus,S.modulus_pos,hmod ▸ hprod,?_⟩
  have hc : S.primes.card = m := hcard
  simpa only [hc] using fixed_modulus_bound S

end RTS
