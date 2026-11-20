module

public import RTS.WeightFamilies

/-! Integer Fourier frequencies in the product of the two trigonometric polynomials in Section 5. -/

@[expose] public section

namespace RTS.Dyadic

open Finset
variable {d : ℕ}

abbrev ProductIndex (d : ℕ) := (Fin d → ℕ) × (Fin d → Finset ℕ)

def testTerms (m r : Fin d → ℕ) : Finset (ProductIndex d) :=
  indexBox m ×ˢ family m r

def productSpace (m : Fin d → ℕ) (p : ProductIndex d) : Fin d → ℤ :=
  frequency m p.1 + spaceFreq m p.2

def productTime (m : Fin d → ℕ) (p : ProductIndex d) : ℤ :=
  (∑ l, frequency m p.1 l ^ 2) + timeFreq m p.2

def collisions (m r : Fin d → ℕ) : Finset (ProductIndex d × ProductIndex d) :=
  ((testTerms m r) ×ˢ (testTerms m r)).filter fun p =>
    productSpace m p.1 = productSpace m p.2 ∧ productTime m p.1 = productTime m p.2

end RTS.Dyadic
