module

public import RTS.LiftingAbel
public import RTS.LiftingResidues
public import RTS.PrimitiveSides

/-! Actual lattice parameter sets used in the rectangular lower bound and the pinned
upper bound. The rectangular direction is additionally truncated at N/(8q). -/
@[expose] public noncomputable section
namespace RTS.Lifting
open Finset

abbrev PinResidue (q : ℕ) := Residue q × ZMod q × ZMod q
abbrev RectResidue (q : ℕ) := Residue q × PinResidue q
def representative {q : ℕ} (w : Residue q) : Point := fun i => (w i).val

def directions (q : ℕ) (a : Residue q) (T : ℝ) : Finset Point :=
  (nonzeroSquare q (representative a) T).filter (fun w => Nat.Coprime (w 0).natAbs (w 1).natAbs)

def picks (q : ℕ) (b c : ZMod q) (Y : ℝ) : Finset (ℤ × ℤ) :=
  ((line q (b.val:ℤ) Y) ×ˢ (line q (c.val:ℤ) Y)).erase (0,0)

def sideFiber (q : ℕ) (e : PinResidue q) (T U : ℝ) : Finset SideParams :=
  (directions q e.1 T).biUnion (fun w =>
    (picks q e.2.1 e.2.2 (U/(radius w:ℝ))).image fun rs => (w,rs))

def pinTupleSet (q : ℕ) (F : Finset (PinResidue q)) (N : ℝ) : Finset SideParams :=
  F.biUnion (fun e => sideFiber q e (4*N) (4*N))

def rectFiber (q : ℕ) (e : RectResidue q) (N : ℝ) : Finset RectParams :=
  pointsInResidue q e.1 (N/4) ×ˢ sideFiber q e.2 (N/(8*q)) (N/4)

def rectTupleSet (q : ℕ) (E : Finset (RectResidue q)) (N : ℝ) : Finset RectParams :=
  E.biUnion (fun e => rectFiber q e N)

abbrev sideResidue (q : ℕ) (p : SideParams) : PinResidue q :=
  (reduce q p.1,(p.2.1 : ZMod q),(p.2.2 : ZMod q))

abbrev rectResidue (q : ℕ) (p : RectParams) : RectResidue q :=
  (reduce q p.1, sideResidue q p.2)

theorem mem_directions {q : ℕ} (hq : 0 < q) {w : Point} {a : Residue q} {T : ℝ} :
    w ∈ directions q a T ↔ Primitive w ∧ (radius w : ℝ) ≤ T ∧ reduce q w = a := by
  change w ∈ ((pointsInResidue q a T).erase 0).filter _ ↔ _
  simp only [mem_filter, mem_erase, mem_pointsInResidue hq, ← radius_le_iff]
  change ((w ≠ 0 ∧ _ ∧ _) ∧ Primitive w) ↔ _
  exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨primitive_ne_zero h.1,h.2⟩,h.1⟩⟩

theorem mem_picks {q : ℕ} (hq : 0 < q) {b c : ZMod q} {Y : ℝ} {r s : ℤ} :
    (r,s) ∈ picks q b c Y ↔ (r ≠ 0 ∨ s ≠ 0) ∧
      |(r:ℝ)| ≤ Y ∧ |(s:ℝ)| ≤ Y ∧ (r:ZMod q) = b ∧ (s:ZMod q) = c := by
  have : NeZero q := ⟨hq.ne'⟩
  simp only [picks, mem_erase, mem_product, mem_line hq,
    ← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hz : (r, s) ≠ ((0,0) : ℤ × ℤ) ↔ r ≠ 0 ∨ s ≠ 0 := by
    simp only [ne_eq, Prod.mk.injEq, not_and_or]
  grind

theorem mem_sideFiber {q : ℕ} (hq : 0 < q) (e : PinResidue q) (T U : ℝ) (p : SideParams) :
    p ∈ sideFiber q e T U ↔
      sideResidue q p = e ∧ Proper p ∧ (radius p.1:ℝ) ≤ T ∧
      |(p.2.1:ℝ)| * (radius p.1:ℝ) ≤ U ∧ |(p.2.2:ℝ)| * (radius p.1:ℝ) ≤ U := by
  obtain ⟨w,r,s⟩ := p
  obtain ⟨a,b,c⟩ := e
  simp only [sideFiber, mem_biUnion, mem_image, Prod.mk.injEq, exists_eq_right_right,
    mem_directions hq, sideResidue, Proper]
  rw [mem_picks hq]
  constructor
  · rintro ⟨⟨hP,hT,ha⟩,hn,hr,hs,hb,hc⟩
    have hρ : 0 < (radius w : ℝ) := by exact_mod_cast radius_pos (primitive_ne_zero hP)
    exact ⟨⟨ha,hb,hc⟩, ⟨hP,hn⟩,hT,(le_div_iff₀ hρ).mp hr,(le_div_iff₀ hρ).mp hs⟩
  · rintro ⟨⟨ha,hb,hc⟩,⟨hP,hn⟩,hT,hr,hs⟩
    have hρ : 0 < (radius w : ℝ) := by exact_mod_cast radius_pos (primitive_ne_zero hP)
    exact ⟨⟨hP,hT,ha⟩,hn,(le_div_iff₀ hρ).mpr hr,(le_div_iff₀ hρ).mpr hs,hb,hc⟩

theorem mem_pinTupleSet {q : ℕ} (hq : 0 < q) (F : Finset (PinResidue q)) (N : ℝ) (p : SideParams) :
    p ∈ pinTupleSet q F N ↔ sideResidue q p ∈ F ∧ Proper p ∧ (radius p.1:ℝ) ≤ 4*N ∧
      |(p.2.1:ℝ)| * (radius p.1:ℝ) ≤ 4*N ∧ |(p.2.2:ℝ)| * (radius p.1:ℝ) ≤ 4*N := by
  simp only [pinTupleSet, mem_biUnion, mem_sideFiber hq]
  aesop

theorem mem_rectTupleSet {q : ℕ} (hq : 0 < q) (E : Finset (RectResidue q)) (N : ℝ) (p : RectParams) :
    p ∈ rectTupleSet q E N ↔ rectResidue q p ∈ E ∧ Proper p.2 ∧
      (radius p.1:ℝ) ≤ N/4 ∧ (radius p.2.1:ℝ) ≤ N/(8*q) ∧
      |(p.2.2.1:ℝ)| * (radius p.2.1:ℝ) ≤ N/4 ∧ |(p.2.2.2:ℝ)| * (radius p.2.1:ℝ) ≤ N/4 := by
  simp only [rectTupleSet, mem_biUnion, rectFiber, mem_product, mem_pointsInResidue hq,
    ← radius_le_iff, mem_sideFiber hq, rectResidue]
  constructor
  · rintro ⟨e,he,⟨hx,hx'⟩,hw,hp,ht,hr,hs⟩
    have heq : (reduce q p.1, sideResidue q p.2) = e := Prod.ext hx' hw
    exact ⟨heq ▸ he,hp,hx,ht,hr,hs⟩
  · rintro ⟨he,hp,hx,ht,hr,hs⟩
    exact ⟨_,he,⟨hx,rfl⟩,rfl,hp,ht,hr,hs⟩


/-- A coordinate interval in a fixed residue contains at least Y/q points
when Y/q ≥ 1. The product gives a uniform lower bound for rectangle origins. -/
theorem x_square_lower {q : ℕ} (hq : 0 < q) (a : Residue q) {Y : ℝ} (hY : 1 ≤ Y/q) :
    (Y/q)^2 ≤ ((pointsInResidue q a Y).card : ℝ) := by
  have hp : 0 < (q:ℝ) := by exact_mod_cast hq
  have hy : 0 ≤ Y := by have := (le_div_iff₀ hp).mp hY; linarith
  have hx (i : Fin 2) : Y/(q:ℝ) ≤ (line q ((a i).val : ℤ) Y).card := by
    have hh := (abs_le.mp (line_card_error hq ((a i).val : ℤ) hy)).1
    linarith only [hh,hY, show 2*Y/(q:ℝ) = 2*(Y/q) by ring]
  simp only [pointsInResidue, square, Fintype.card_piFinset, Fin.prod_univ_two, Nat.cast_mul]
  rw [sq]
  exact mul_le_mul (hx 0) (hx 1) (by positivity) (by positivity)

end RTS.Lifting
