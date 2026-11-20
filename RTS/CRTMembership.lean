module

public import RTS.CRT
public import RTS.PrimitiveSides

/-! # Geometric membership tests modulo the composite modulus -/
@[expose] public noncomputable section
namespace RTS.CRT.PrimeSet
open Finset FieldCounts
variable (P : PrimeSet)

section
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem mem_localFiber (choices : Plane K → Finset (K × K)) (w : Plane K) (rs : K × K) :
    (w,rs) ∈ localFiber choices ↔ w ≠ 0 ∧ rs ∈ choices w := by
  simp [localFiber]

theorem mem_localQuad (choices : Plane K → Plane K → Finset (K × K))
    (x w : Plane K) (rs : K × K) : (x,w,rs) ∈ localQuad choices ↔
    lengthSq x = 1 ∧ w ≠ 0 ∧ rs ∈ choices x w := by
  simp [localQuad,mem_localFiber,lengthSq, and_assoc, and_left_comm,and_comm]

omit [DecidableEq K] in
private theorem mem_rectChoices (x w : Plane K) (r s : K) :
    (r,s) ∈ rectChoices x w ↔ RectAt x w r s := by classical simp [rectChoices]
private theorem mem_triangleChoices (x w : Plane K) (r s : K) :
    (r,s) ∈ triangleChoices x w ↔ TriAt x w r s := by classical simp [triangleChoices]
private theorem mem_pinChoices (x w : Plane K) (r s : K) :
    (r,s) ∈ pinChoices x w ↔ PinAt x w r s := by classical simp [pinChoices]

end

def goodDirection (w : P.Pt) : Prop := ∀ p, P.planeEquiv w p ≠ 0

def turn (w : P.Pt) : P.Pt := ![-w 1,w 0]

/-- The unique residue whose CRT coordinates are the inverses of two. -/
def half : P.R := P.scalarEquiv.symm fun _ => (2 : _)⁻¹

theorem two_mul_half : 2 * P.half = 1 := by
  apply P.scalarEquiv.injective
  ext p
  have h₂ : (2 : P.Local p) ≠ 0 := by
    intro h
    apply norm_ne_zero p (P.three p p.property) (w := (1,1)) (by simp)
    simpa [lengthSq,one_add_one_eq_two] using h
  have h2eq : P.scalarEquiv 2 p = (2:P.Local p) := by
    rw [show (2:P.R) = 1+1 by ring, map_add, map_one]; exact one_add_one_eq_two
  simpa [half,h2eq] using mul_inv_cancel₀ h₂

@[simp] theorem project_add (x y : P.Pt) (p) :
    P.planeEquiv (x+y) p = P.planeEquiv x p + P.planeEquiv y p := by
  ext <;> simp [planeEquiv]
@[simp] theorem project_sub (x y : P.Pt) (p) :
    P.planeEquiv (x-y) p = P.planeEquiv x p - P.planeEquiv y p := by
  ext <;> simp [planeEquiv]
@[simp] theorem project_smul (r : P.R) (x : P.Pt) (p) :
    P.planeEquiv (r • x) p = P.scalarEquiv r p • P.planeEquiv x p := by
  ext <;> simp [planeEquiv, Pi.smul_apply, smul_eq_mul]
@[simp] theorem project_turn (x : P.Pt) (p) :
    P.planeEquiv (P.turn x) p = quarterTurn (P.planeEquiv x p) := by
  ext <;> simp [turn,planeEquiv,quarterTurn]
@[simp] theorem project_half (p) : P.scalarEquiv P.half p = (2:P.Local p)⁻¹ := by simp [half]

theorem circle_local_iff (x : P.Pt) :
    x ∈ P.circle ↔ ∀ p, lengthSq (P.planeEquiv x p) = 1 := by
  rw [circle, mem_lift]; simp only [mem_localCircle,lengthSq]

theorem rects_iff (x w : P.Pt) (r s : P.R) :
    (x,w,r,s) ∈ P.rects ↔ P.goodDirection w ∧ x ∈ P.circle ∧
      x+r•w ∈ P.circle ∧ x+s•P.turn w ∈ P.circle ∧ x+r•w+s•P.turn w ∈ P.circle := by
  rw [rects, mem_lift]
  change (∀ p, (P.planeEquiv x p,P.planeEquiv w p,P.scalarEquiv r p,P.scalarEquiv s p) ∈
    localQuad rectChoices) ↔ _
  simp only [mem_localQuad,mem_rectChoices,RectAt,circle_local_iff,
    project_add,project_smul,project_turn,goodDirection,forall_and]
  all_goals tauto

theorem tris_iff (x w : P.Pt) (r s : P.R) :
    (x,w,r,s) ∈ P.tris ↔ P.goodDirection w ∧ x ∈ P.circle ∧
      x+r•w ∈ P.circle ∧ x+P.half•(r•w+s•P.turn w) ∈ P.circle := by
  rw [tris, mem_lift]
  change (∀ p, (P.planeEquiv x p,P.planeEquiv w p,P.scalarEquiv r p,P.scalarEquiv s p) ∈
    localQuad triangleChoices) ↔ _
  simp only [mem_localQuad,mem_triangleChoices,TriAt,circle_local_iff,
    project_add,project_smul,project_turn,project_half,goodDirection,forall_and]
  all_goals tauto

theorem pins_iff (k w : P.Pt) (r s : P.R) :
    (w,r,s) ∈ P.pins k ↔ P.goodDirection w ∧
      k-P.half•(r•w+s•P.turn w) ∈ P.circle ∧ k+P.half•(r•w-s•P.turn w) ∈ P.circle := by
  rw [pins, mem_lift]
  change (∀ p, (P.planeEquiv w p,P.scalarEquiv r p,P.scalarEquiv s p) ∈
    localFiber (pinChoices (P.planeEquiv k p))) ↔ _
  simp only [mem_localFiber,mem_pinChoices,PinAt,circle_local_iff,
    project_sub,project_add,project_smul,project_turn,project_half,goodDirection,forall_and]

/-- Integer primitive directions are nonzero in every prime-field plane. -/
theorem primitive_goodDirection {w : Point} (hw : Lifting.Primitive w) :
    P.goodDirection (fun i => (w i : P.R)) := by
  intro p hzero
  have aux (n : ℤ) (hn : (n:P.Local p) = 0) : (p:ℕ) ∣ n.natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp hn))
  have h₀ : (w 0 : P.Local p) = 0 := by simpa [planeEquiv] using congrArg Prod.fst hzero
  have h₁ : (w 1 : P.Local p) = 0 := by simpa [planeEquiv] using congrArg Prod.snd hzero
  have hd := Nat.dvd_gcd (aux _ h₀) (aux _ h₁)
  rw [show Nat.gcd (w 0).natAbs (w 1).natAbs = 1 from hw] at hd
  exact (P.prime p p.property).ne_one (Nat.dvd_one.mp hd)

/-- Every common divisor of a good direction is coprime to the composite modulus. -/
theorem content_coprime {w : Point} (hw : P.goodDirection (fun i => (w i : P.R))) :
    (Nat.gcd (w 0).natAbs (w 1).natAbs).Coprime P.modulus := by
  unfold modulus
  apply Nat.coprime_prod_right_iff.mpr
  intro p _
  apply Nat.Coprime.symm
  apply (P.prime p p.property).coprime_iff_not_dvd.mpr
  intro hd
  have h₁ := hd.trans (Nat.gcd_dvd_left (w 0).natAbs (w 1).natAbs)
  have h₂ := hd.trans (Nat.gcd_dvd_right (w 0).natAbs (w 1).natAbs)
  have aux (n : ℤ) (hn : (p:ℕ) ∣ n.natAbs) : (n:P.Local p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mpr (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hn))
  apply hw p
  exact Prod.ext (by simpa [planeEquiv] using aux (w 0) h₁) (by simpa [planeEquiv] using aux (w 1) h₂)

theorem circle_nonempty : P.circle.Nonempty :=
  ⟨![1,0], by rw [circle_iff]; simp⟩

theorem max_pins_card :
    (P.circle.sup (fun k => (P.pins k).card)) = ∏ p : ↥P.primes, 3*((p:ℕ)-1)*p := by
  calc
    _ = P.circle.sup (fun _ => ∏ p : ↥P.primes, 3*((p:ℕ)-1)*p) :=
      Finset.sup_congr rfl fun k hk => P.pins_card k hk
    _ = _ := Finset.sup_const P.circle_nonempty _

theorem rect_max_pin_ratio :
    (P.rects.card : ℝ) / (P.circle.card * (P.circle.sup fun k => (P.pins k).card : ℕ)) =
      (4/3:ℝ)^P.primes.card := by
  obtain ⟨k,hk⟩ := P.circle_nonempty
  rw [P.max_pins_card, ← P.pins_card k hk]
  exact P.rect_pin_ratio k hk

end RTS.CRT.PrimeSet
