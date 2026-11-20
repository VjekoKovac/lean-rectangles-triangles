module

public import Std

@[expose] public section

/-!
An independent Fourier coefficient check of Lemma 5.1 at m=(3,2).
The offsets are 0 and 3. As both half-sizes equal 1, the auxiliary
polynomial f has the same six atoms as u. Enumeration counts the surviving
integer Fourier frequencies exactly, without quadrature.
-/
namespace RTSReview.TwoBlock

abbrev Point := Int × Int
abbrev Atom := Int × Int × Int

def points : List Point :=
  ([2,4,8] : List Int).flatMap fun x => ([16,32] : List Int).map (fun y => (x,y))
def energy (k : Point) : Int := k.1 ^ 2 + k.2 ^ 2
def mode (k l : Point) : Atom := (k.1+l.1, k.2+l.2, energy k + energy l)
def modes : List Atom := points.flatMap (fun k => points.map (mode k))
/-- Number of ordered coincidences of a list allowing repetitions. -/
def pairs {α} [BEq α] (xs : List α) : Nat :=
  (xs.map (fun x => (xs.filter (fun y => x == y)).length)).sum
def alongRay (k l : Point) : Int :=
  energy l - 2 * (k.1*l.1 + k.2*l.2)

set_option maxRecDepth 10000 in
theorem check_two_blocks :
    points.length = 6 ∧
    points.map (fun k => pairs (points.map (alongRay k))) = [6,6,6,6,6,6] ∧
    pairs modes = 90 ∧ 48 ≤ pairs modes := by decide

#print axioms check_two_blocks
end RTSReview.TwoBlock
