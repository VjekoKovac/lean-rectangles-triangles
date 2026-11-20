module

public import Std

@[expose] public section

/-!
Independent sanity check of the four parametrized counts of Lemma 2.2 at
the smallest permitted prime. Arithmetic uses residues modulo three. The
tuples (x,w,r,s) are enumerated directly, with a separate per-apex enumeration.
This file has no dependency on the solution.
-/
namespace RTSReview.PrimeThree

abbrev R := Fin 3
abbrev P := R × R

def residues : List R := [0, 1, 2]
def points : List P := residues.flatMap (fun a => residues.map (fun b => (a,b)))
def circle (x : P) : Bool := x.1 * x.1 + x.2 * x.2 == 1
def members : List P := points.filter circle
def directions : List P := points.filter (fun w => w != (0, 0))
def add (x y : P) : P := (x.1 + y.1, x.2 + y.2)
def mul (r : R) (x : P) : P := (r * x.1, r * x.2)
def rot (x : P) : P := (-x.2, x.1)

def sumOn {α} (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum

def overDirections (test : P → P → Bool) : Nat :=
  sumOn directions fun w => sumOn residues fun r => sumOn residues fun s =>
    if test (mul r w) (mul s (rot w)) then 1 else 0

def rectangles : Nat := sumOn members fun x => overDirections fun u v =>
  circle (add x u) && circle (add x v) && circle (add (add x u) v)

def triangles : Nat := sumOn members fun x => overDirections fun u v =>
  circle (add x u) && circle (add x (mul 2 (add u v)))

def atApex (k : P) : Nat := overDirections fun u v =>
  -- In F₃, 2⁻¹ = 2. The first endpoint is k − (u+v)/2.
  let x := add k (mul (-2) (add u v))
  circle x && circle (add x u)

set_option maxRecDepth 10000 in
theorem check_prime_three :
    members.length = 4 ∧ rectangles = 96 ∧ triangles = 72 ∧
    members.map atApex = [18, 18, 18, 18] := by decide

#print axioms check_prime_three
end RTSReview.PrimeThree
