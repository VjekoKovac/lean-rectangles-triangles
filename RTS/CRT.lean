module

public import RTS.FieldCounts
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Data.Fintype.BigOperators

/-! # Chinese remaindering of the circle configurations

The global sets contain actual coordinates modulo the product of the primes.
The inverse CRT map transports the product of local parameter sets into these
coordinates. Its forward map is `ZMod.castHom` in every coordinate.
-/
@[expose] public noncomputable section
namespace RTS.CRT
open Finset FieldCounts

structure PrimeSet where
  primes : Finset ℕ
  prime : ∀ p ∈ primes, Nat.Prime p
  three : ∀ p ∈ primes, p % 4 = 3

namespace PrimeSet
variable (P : PrimeSet)

def modulus := ∏ p : ↥P.primes, (p : ℕ)
abbrev R := ZMod P.modulus
abbrev Pt := Fin 2 → P.R
abbrev Local (p : ↥P.primes) := ZMod (p : ℕ)

instance modulusPrime (p : ↥P.primes) : Fact (p : ℕ).Prime := ⟨P.prime p p.property⟩

def scalarEquiv : P.R ≃+* (∀ p : ↥P.primes, P.Local p) :=
  ZMod.prodEquivPi (fun p : ↥P.primes => (p:ℕ)) (fun i j h =>
    (Nat.coprime_primes (P.prime i i.property) (P.prime j j.property)).2 (fun e => h (Subtype.ext e)))

/-- Grouping two cyclic coordinates by prime gives a prime-indexed tuple of planes. -/
def planeEquiv : P.Pt ≃ (∀ p : ↥P.primes, Plane (P.Local p)) where
  toFun x p := (P.scalarEquiv (x 0) p, P.scalarEquiv (x 1) p)
  invFun x := ![P.scalarEquiv.symm (fun p => (x p).1),P.scalarEquiv.symm (fun p => (x p).2)]
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv x := by funext p; simp

def pairEquiv {ι A B : Type*} {U V : ι → Type*}
    (e : A ≃ (∀ i,U i)) (f : B ≃ (∀ i,V i)) : A × B ≃ (∀ i, U i × V i) where
  toFun x i := (e x.1 i, f x.2 i)
  invFun y := (e.symm (fun i => (y i).1), f.symm (fun i => (y i).2))
  left_inv x := by simp
  right_inv x := by funext i; simp

abbrev PinIndex (K : Type*) := (Fin 2 → K) × (K × K)
abbrev QuadIndex (K : Type*) := (Fin 2 → K) × PinIndex K

def pinEquiv : PinIndex P.R ≃ (∀ p : ↥P.primes, Plane (P.Local p) × (P.Local p × P.Local p)) :=
  pairEquiv P.planeEquiv (pairEquiv P.scalarEquiv.toEquiv P.scalarEquiv.toEquiv)

def quadEquiv : QuadIndex P.R ≃ (∀ p : ↥P.primes, Plane (P.Local p) ×
    (Plane (P.Local p) × (P.Local p × P.Local p))) :=
  pairEquiv P.planeEquiv P.pinEquiv

section LocalCounts
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

def localCircle : Finset (Plane K) := Finset.univ.map (Function.Embedding.subtype _ : UnitCircle K ↪ Plane K)

theorem mem_localCircle {x : Plane K} : x ∈ localCircle ↔ x.1^2 + x.2^2 = 1 := by
  simp [localCircle]

def localFiber (choices : Plane K → Finset (K × K)) : Finset (Plane K × (K × K)) :=
  (((Finset.univ : Finset (Plane K)).erase 0).sigma choices).map
    ⟨fun z => (z.1,z.2), by intro ⟨a,b⟩ ⟨x,y⟩ h; obtain ⟨rfl,rfl⟩ := Prod.ext_iff.mp h; rfl⟩

def localQuad (choices : Plane K → Plane K → Finset (K × K)) :
    Finset (Plane K × (Plane K × (K × K))) :=
  ((Finset.univ : Finset (UnitCircle K)).sigma (fun x => localFiber (choices x))).map
    ⟨fun z => ((z.1:Plane K),z.2), by
      intro ⟨a,b⟩ ⟨x,y⟩ h
      obtain ⟨hx,rfl⟩ := Prod.ext_iff.mp h
      obtain rfl := Subtype.ext hx
      rfl⟩

theorem localQuad_card (choices : Plane K → Plane K → Finset (K × K)) :
    (localQuad choices).card = ∑ x : UnitCircle K, ∑ w ∈ Finset.univ.erase 0, (choices x w).card := by
  simp [localQuad,localFiber,Finset.card_sigma]

theorem localFiber_card (choices : Plane K → Finset (K × K)) :
    (localFiber choices).card = ∑ w ∈ Finset.univ.erase 0, (choices w).card := by
  simp [localFiber,Finset.card_sigma]

end LocalCounts

def lift {ι A : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    (e : A ≃ (∀ i,B i)) (s : ∀ i, Finset (B i)) : Finset A :=
  (Fintype.piFinset s).map e.symm.toEmbedding

theorem mem_lift {ι A : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    (e : A ≃ (∀ i,B i)) (s : ∀ i, Finset (B i)) (x : A) :
    x ∈ lift e s ↔ ∀ i, e x i ∈ s i := by
  classical
  simp [lift,Fintype.mem_piFinset]

def circle : Finset P.Pt := lift P.planeEquiv (fun _ => localCircle)
def rects : Finset (QuadIndex P.R) := lift P.quadEquiv (fun _ => localQuad rectChoices)
def tris : Finset (QuadIndex P.R) := lift P.quadEquiv (fun _ => localQuad triangleChoices)
def pins (k : P.Pt) : Finset (PinIndex P.R) :=
  lift P.pinEquiv (fun p => localFiber (pinChoices (P.planeEquiv k p)))

theorem circle_iff (k : P.Pt) : k ∈ P.circle ↔ k 0 ^ 2 + k 1 ^ 2 = 1 := by
  rw [circle, mem_lift]
  simp only [mem_localCircle]
  change (∀ p, (P.scalarEquiv (k 0) p)^2 + (P.scalarEquiv (k 1) p)^2 = 1) ↔ _
  rw [← P.scalarEquiv.injective.eq_iff (a := (k 0)^2 + (k 1)^2) (b := 1)]
  simp [funext_iff]

theorem circle_card : P.circle.card = ∏ p : ↥P.primes, ((p:ℕ)+1) := by
  simp only [circle,lift,card_map,Fintype.card_piFinset,localCircle,card_univ]
  apply prod_congr rfl
  intro p _
  exact card_unitCircle p (P.three p p.property)

theorem rects_card : P.rects.card = ∏ p : ↥P.primes, 4*((p:ℕ)-1)*p*(p+1) := by
  simp only [rects,lift,card_map,Fintype.card_piFinset,localQuad_card]
  apply prod_congr rfl
  intro p _
  exact rectangles_card p (P.three p p.property)

theorem tris_card : P.tris.card = ∏ p : ↥P.primes, 3*((p:ℕ)-1)*p*(p+1) := by
  simp only [tris,lift,card_map,Fintype.card_piFinset,localQuad_card]
  apply prod_congr rfl
  intro p _
  exact triangles_card p (P.three p p.property)

theorem pins_card (k : P.Pt) (hk : k ∈ P.circle) :
    (P.pins k).card = ∏ p : ↥P.primes, 3*((p:ℕ)-1)*p := by
  simp only [pins,lift,card_map,Fintype.card_piFinset,localFiber_card]
  have h := (mem_lift P.planeEquiv (fun _ => localCircle) k).mp hk
  apply prod_congr rfl
  intro p _
  exact
    pinnedTriangles_card p (P.three p p.property) ⟨P.planeEquiv k p,mem_localCircle.mp (h p)⟩


private theorem ratio_each (p : ↥P.primes) :
    (((4 * ((p:ℕ)-1) * p * (p+1) : ℕ) : ℝ) /
      ((3 * ((p:ℕ)-1) * p * (p+1) : ℕ) : ℝ)) = 4/3 := by
  have h1 : 0 < (p:ℕ)-1 := by have := (P.prime p p.property).two_le; omega
  have h2 := (P.prime p p.property).pos
  push_cast
  field_simp

/-- The ordinary and the pinned denominators agree for every admissible apex. -/
theorem pin_denominator (k : P.Pt) (hk : k ∈ P.circle) :
    P.circle.card * (P.pins k).card = P.tris.card := by
  rw [circle_card, pins_card _ _ hk, tris_card, ← Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro p _
  ring

theorem rect_tri_ratio :
    (P.rects.card : ℝ) / P.tris.card = (4/3:ℝ)^P.primes.card := by
  rw [rects_card,tris_card]
  simp only [Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  simp only [P.ratio_each,Finset.prod_const,Finset.card_univ,Fintype.card_coe]

theorem rect_pin_ratio (k : P.Pt) (hk : k ∈ P.circle) :
    (P.rects.card : ℝ) / (P.circle.card * (P.pins k).card) = (4/3:ℝ)^P.primes.card := by
  rw [← Nat.cast_mul, P.pin_denominator k hk, P.rect_tri_ratio]

end PrimeSet
end RTS.CRT
