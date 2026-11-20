module

public import RTS.Combinatorics
public import Mathlib.Data.Fin.VecNotation

/-! A small check on the project's actual counting definitions. Different apices
have different counts, so the check distinguishes the two denominators. -/
@[expose] public section

namespace RTSReview.OrderedCounts
open RTS

def o : Point := ![0,0]
def north : Point := ![0,1]
def east : Point := ![1,0]
def A : Finset Point := {o, north, east}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem check_ordered_counts :
    A.card = 3 ∧ rectangleCount A = 15 ∧ triangleCount A = 11 ∧
    pinnedTriangleCount A o = 5 ∧ pinnedTriangleCount A north = 3 ∧
    pinnedTriangleCount A east = 3 ∧ A.card * maxPinnedCount A = 15 := by decide

#print axioms check_ordered_counts
end RTSReview.OrderedCounts
