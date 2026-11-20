module

public import RTS.GeometricResidues
public import RTS.LiftingTuples

/-! Passage between the finite sets used in lattice summation and the integer counts
used in the introductory theorem. -/
@[expose] public noncomputable section
namespace RTS.Lifting

variable (P : CRT.PrimeSet)

private theorem modulus_positive : 0 < P.modulus :=
  Finset.prod_pos (fun p _ => (P.prime p p.property).pos)

theorem rect_tuple_count_le (N : ℕ) :
    (rectTupleSet P.modulus P.rects N).card ≤ 2 * rectangleCount (circleLift P.modulus N) := by
  apply rectParams_card_le
  · intro p hp
    exact ((mem_rectTupleSet (modulus_positive P) ..).mp hp).2.1
  · rintro ⟨x,w,r,s⟩ hp
    obtain ⟨hres,_,hx,_,hr,hs⟩ := (mem_rectTupleSet (modulus_positive P) ..).mp hp
    exact sample_corners_mem P hres hx hr hs

theorem pin_count_le_tuples {N : ℕ} {k : Point} (hk : k ∈ circleLift P.modulus N) :
    pinnedTriangleCount (circleLift P.modulus N) k ≤
      (pinTupleSet P.modulus (P.pins (reduce P.modulus k)) N).card + 1 := by
  apply pinned_count_le_params
  rintro a ha b hb _ ⟨w,r,s⟩ hp he
  apply (mem_pinTupleSet (modulus_positive P) ..).2
  exact ⟨pin_residue P ha hb hp.1 he,hp,pin_sizes P ha hb hk hp.2 he⟩

end RTS.Lifting
