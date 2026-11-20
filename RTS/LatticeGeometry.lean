module

public import RTS.PrimitiveSides
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Comparison of the ordered lattice configurations with finite lists of primitive
direction parameters. Diagonal pairs at the prescribed apex are counted separately. -/
@[expose] public noncomputable section
namespace RTS.Lifting

open Finset
local instance (a b c e : Point) : Decidable (IsRectangle a b c e) :=
  inferInstanceAs (Decidable (a+c=b+e ∧ dot₂ (b-a) (e-a) = 0))
local instance (a b k : Point) : Decidable (IsTriangle a b k) :=
  inferInstanceAs (Decidable (dot₂ (2 • k-a-b) (b-a) = 0))

def corners (p : RectParams) : Point × Point × Point × Point :=
  let u := (sides p.2).1
  let v := (sides p.2).2
  (p.1,p.1+u,p.1+u+v,p.1+v)

def rectangles (A : Finset Point) : Finset (Point × Point × Point × Point) :=
  (A ×ˢ (A ×ˢ (A ×ˢ A))).filter fun y => IsRectangle y.1 y.2.1 y.2.2.1 y.2.2.2

theorem rectangles_card (A : Finset Point) : (rectangles A).card = rectangleCount A := by
  rw [rectangles, Finset.card_filter]
  simp only [rectangleCount, card_filter, sum_product, IsRectangle]
  rfl

theorem corners_rectangle (p : RectParams) :
    IsRectangle (corners p).1 (corners p).2.1 (corners p).2.2.1 (corners p).2.2.2 := by
  constructor
  · dsimp [corners]; abel
  · simp only [corners, sides, add_sub_cancel_left, dot₂, Fin.sum_univ_two, 
      zsmul_eq_mul, rot]
    simp
    ring

/-- Pigeonhole bound for any chosen list of the paper's rectangle parameters. -/
theorem rectParams_card_le (A : Finset Point) (P : Finset RectParams)
    (hp : ∀ p ∈ P, Proper p.2)
    (hA : ∀ p ∈ P, (corners p).1 ∈ A ∧ (corners p).2.1 ∈ A ∧
        (corners p).2.2.1 ∈ A ∧ (corners p).2.2.2 ∈ A) :
    P.card ≤ 2 * rectangleCount A := by
  classical
  rw [← rectangles_card]
  apply card_le_mul_card_image_of_maps_to (f := corners)
  · intro p h
    simpa only [rectangles, mem_filter, mem_product, corners_rectangle, and_true] using hA p h
  intro y _
  let B := P.filter (fun p => corners p = y)
  change B.card ≤ 2
  rcases B.eq_empty_or_nonempty with hh|⟨p₀,h₀⟩
  · simp [hh]
  have hp₀ := (mem_filter.mp h₀).1
  have he₀ := (mem_filter.mp h₀).2
  have hsub : B ⊆ {p₀, (p₀.1, flip p₀.2)} := by
    intro p hy
    obtain ⟨hp',he⟩ := mem_filter.mp hy
    have hcorn := he.trans he₀.symm
    have hx : p.1 = p₀.1 := congrArg (fun q : Point × Point × Point × Point => q.1) hcorn
    have h₁ := congrArg (fun q : Point × Point × Point × Point => q.2.1) hcorn
    have h₂ := congrArg (fun q : Point × Point × Point × Point => q.2.2.2) hcorn
    change p.1 + (sides p.2).1 = p₀.1 + (sides p₀.2).1 at h₁
    change p.1 + (sides p.2).2 = p₀.1 + (sides p₀.2).2 at h₂
    rw [hx] at h₁ h₂
    have hs := sides_fiber (hp _ hp') (hp _ hp₀) (Prod.ext (add_left_cancel h₁) (add_left_cancel h₂))
    rcases hs with h|h
    · exact mem_insert.mpr (Or.inl (Prod.ext hx h))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Prod.ext hx h)))
  exact (card_le_card hsub).trans (by simpa only [card_singleton] using card_insert_le p₀ {(p₀.1,flip p₀.2)})

def pinBases (A : Finset Point) (k : Point) : Finset (Point × Point) :=
  (A ×ˢ A).filter (fun y => IsTriangle y.1 y.2 k)

theorem pinBases_card (A : Finset Point) (k : Point) :
    (pinBases A k).card = pinnedTriangleCount A k := by
  rw [pinBases, Finset.card_filter]
  simp only [pinnedTriangleCount, card_filter, sum_product, IsTriangle]
  rfl

def triangleSides (k : Point) (p : Point × Point) : Point × Point :=
  (p.2-p.1, 2 • k - p.1 - p.2)

theorem triangleSides_injective (k : Point) : Function.Injective (triangleSides k) := by
  rintro ⟨a,b⟩ ⟨c,e⟩ he
  have h₁ : b-a = e-c := congrArg Prod.fst he
  have h₂ : 2 • k - a - b = 2 • k - c - e := congrArg Prod.snd he
  have aux (i : Fin 2) : a i = c i ∧ b i = e i := by
    have hx : b i - a i = e i - c i := congrFun h₁ i
    have hy : 2 * k i - a i - b i = 2 * k i - c i - e i := congrFun h₂ i
    omega
  exact Prod.ext (funext fun i => (aux i).1) (funext fun i => (aux i).2)

theorem triangle_param {a b k : Point} (ht : IsTriangle a b k)
    (hne : triangleSides k (a,b) ≠ (0,0)) :
    ∃ p : SideParams, Proper p ∧ sides p = triangleSides k (a,b) := by
  apply perpendicular_sides
  ·
    change dot₂ (b-a) (2 • k-a-b) = 0
    simpa only [IsTriangle, dot₂, mul_comm] using ht
  · by_contra! h
    exact hne (Prod.ext h.1 h.2)

/-- A finite list covering all primitive representations of interest bounds the pinned
triangle count, with a single extra pair for `a=b=k`. The parity test on reconstructed
endpoints may be dropped when forming the covering list. -/
theorem pinned_count_le_params (A : Finset Point) (k : Point) (Q : Finset SideParams)
    (hc : ∀ a ∈ A, ∀ b ∈ A, IsTriangle a b k → ∀ p : SideParams,
      Proper p → sides p = triangleSides k (a,b) → p ∈ Q) :
    pinnedTriangleCount A k ≤ Q.card + 1 := by
  classical
  rw [← pinBases_card, ← card_image_of_injective _ (triangleSides_injective k)]
  have hs : (pinBases A k).image (triangleSides k) ⊆ insert (0,0) (Q.image sides) := by
    intro y hy
    obtain ⟨⟨a,b⟩,ha,rfl⟩ := mem_image.mp hy
    obtain ⟨hab,htri⟩ := mem_filter.mp ha
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    by_cases he : triangleSides k (a,b) = (0,0)
    · exact mem_insert.mpr (Or.inl he)
    obtain ⟨p,hp,he'⟩ := triangle_param htri he
    exact mem_insert.mpr (Or.inr (mem_image.mpr ⟨p,hc a ha b hb htri p hp he',he'⟩))
  exact (card_le_card hs).trans ((card_insert_le _ _).trans (Nat.add_le_add_right card_image_le 1))

end RTS.Lifting
