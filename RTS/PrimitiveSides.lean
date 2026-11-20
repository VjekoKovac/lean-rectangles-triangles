module

public import RTS.Combinatorics
public import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-! Primitive-direction parametrization of perpendicular integer sides in §2.3.
It covers zero first sides and zero second sides. -/
@[expose] public section

namespace RTS.Lifting

abbrev SideParams := Point × ℤ × ℤ
abbrev RectParams := Point × SideParams

def rot (w : Point) : Point := ![-w 1,w 0]

def Primitive (w : Point) : Prop := Nat.Coprime (w 0).natAbs (w 1).natAbs

def sides (p : SideParams) : Point × Point :=
  (p.2.1 • p.1, p.2.2 • rot p.1)

def Proper (p : SideParams) : Prop := Primitive p.1 ∧ (p.2.1 ≠ 0 ∨ p.2.2 ≠ 0)

theorem primitive_iff (w : Point) : Primitive w ↔ Int.gcd (w 0) (w 1) = 1 := Iff.rfl

theorem primitive_ne_zero {w : Point} (hw : Primitive w) : w ≠ 0 := by
  rintro rfl
  simp [Primitive] at hw

@[simp] theorem rot_rot (w : Point) : rot (rot w) = -w := by
  funext i; fin_cases i <;> simp [rot]

@[simp] theorem rot_neg (w : Point) : rot (-w) = -rot w := by
  funext i; fin_cases i <;> simp [rot]

@[simp] theorem rot_smul (r : ℤ) (w : Point) : rot (r • w) = r • rot w := by
  funext i; fin_cases i <;> simp [rot]

theorem primitive_rot {w : Point} (hw : Primitive w) : Primitive (rot w) := by
  simpa [Primitive, rot, Nat.coprime_comm] using hw

theorem primitive_neg {w : Point} (hw : Primitive w) : Primitive (-w) := by
  simpa [Primitive] using hw

/-- Divide the coordinates by their gcd. The multiplier is strictly positive. -/
theorem primitive_factor {z : Point} (hz : z ≠ 0) :
    ∃ (w : Point) (g : ℤ), Primitive w ∧ 0 < g ∧ z = g • w := by
  have hg : 0 < Int.gcd (z 0) (z 1) := by
    by_contra! hh
    obtain ⟨h₀,h₁⟩ := Int.gcd_eq_zero_iff.mp (Nat.le_zero.mp hh)
    exact hz (by funext i; fin_cases i <;> assumption)
  obtain ⟨g,a,b,hg',hab,h₁,h₂⟩ := Int.exists_gcd_one' hg
  refine ⟨![a,b],g,hab,by exact_mod_cast hg',?_⟩
  funext i
  fin_cases i <;> simpa [zsmul_eq_mul, mul_comm] using (by first | exact h₁ | exact h₂ : _)

/-- Bézout's identity gives an integer, not just rational, coordinate along Jw. -/
theorem perp_integer_multiple {w h : Point} (hw : Primitive w) (hh : dot₂ w h = 0) :
    ∃ s : ℤ, h = s • rot w := by
  obtain ⟨a,b,hab⟩ := Int.isCoprime_iff_gcd_eq_one.mpr ((primitive_iff _).mp hw)
  simp only [dot₂, Fin.sum_univ_two] at hh
  refine ⟨a*h 1 - b*h 0, ?_⟩
  funext i; fin_cases i
  · change h 0 = (a * h 1 - b * h 0) * (-w 1)
    linear_combination a * hh - h 0 * hab
  · change h 1 = (a * h 1 - b * h 0) * w 0
    linear_combination b * hh - h 1 * hab

theorem perpendicular_sides {u v : Point} (huv : dot₂ u v = 0) (hne : u ≠ 0 ∨ v ≠ 0) :
    ∃ p : SideParams, Proper p ∧ sides p = (u,v) := by
  by_cases h : u = 0
  · subst u
    obtain ⟨w,s,hw,hs,hv⟩ := primitive_factor (hne.resolve_left (by simp))
    exact ⟨(-rot w,0,s),⟨primitive_neg (primitive_rot hw),Or.inr hs.ne'⟩,
      by simp [sides, hv]⟩
  · obtain ⟨w,r,hw,hr,hu⟩ := primitive_factor h
    have ho : r * dot₂ w v = 0 := by
      rw [hu] at huv
      simp only [dot₂, Fin.sum_univ_two] at huv ⊢
      change r * w 0 * v 0 + r * w 1 * v 1 = 0 at huv
      linear_combination huv
    obtain ⟨s,hv⟩ := perp_integer_multiple hw ((mul_eq_zero.mp ho).resolve_left hr.ne')
    exact ⟨(w,r,s),⟨hw,Or.inl hr.ne'⟩,Prod.ext hu.symm hv.symm⟩

private theorem smul_injective_scalar {w : Point} (hw : Primitive w) :
    Function.Injective (fun r : ℤ => r • w) := by
  intro r s he
  have hn := primitive_ne_zero hw
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hn
  exact mul_right_cancel₀ hi (congrFun he i)

private theorem smul_injective_vec {r : ℤ} (hr : r ≠ 0) :
    Function.Injective (fun w : Point => r • w) := by
  intro x y h
  exact funext fun i => mul_left_cancel₀ hr (congrFun h i)

private theorem direction_unique {w z : Point} (hw : Primitive w) (hz : Primitive z)
    {r s : ℤ} (hr : r ≠ 0) (he : r • w = s • z) : w = z ∨ w = -z := by
  have h₀ : r * w 0 = s * z 0 := congrFun he 0
  have h₁ : r * w 1 = s * z 1 := congrFun he 1
  have hc := congrArg₂ Int.gcd h₀ h₁
  simp only [Int.gcd_mul_left, (primitive_iff _).mp hw, (primitive_iff _).mp hz, mul_one] at hc
  obtain e | e := Int.natAbs_eq_natAbs_iff.mp hc
  · subst s
    exact Or.inl (smul_injective_vec hr he)
  · have es : s = -r := by omega
    rw [es, neg_smul] at he
    exact Or.inr (smul_injective_vec hr (by simpa only [smul_neg] using he))

def flip (p : SideParams) : SideParams := (-p.1,-p.2.1,-p.2.2)

@[simp] theorem sides_flip (p : SideParams) : sides (flip p) = sides p := by
  simp [sides, flip]

/-- Every nonzero orthogonal pair has at most the two parameter tuples related by
simultaneously reversing the primitive direction and the scalar signs. -/
theorem sides_fiber {p q : SideParams} (hp : Proper p) (hq : Proper q)
    (he : sides p = sides q) : p = q ∨ p = flip q := by
  obtain ⟨w,r,s⟩ := p
  obtain ⟨v,a,b⟩ := q
  obtain ⟨hw,hne⟩ := hp
  obtain ⟨hv,_⟩ := hq
  have h₁ : r • w = a • v := congrArg Prod.fst he
  have h₂ : s • rot w = b • rot v := congrArg Prod.snd he
  have hdir : w = v ∨ w = -v := by
    rcases hne with hr|hs
    · exact direction_unique hw hv hr h₁
    · have h' := congrArg rot h₂
      simp only [rot_smul,rot_rot,smul_neg,neg_inj] at h'
      exact direction_unique hw hv hs h'
  rcases hdir with h|h
  · subst w
    exact Or.inl (by rw [smul_injective_scalar hv h₁, smul_injective_scalar (primitive_rot hv) h₂])
  · subst w
    have ha : r = -a := smul_injective_scalar hv (by simpa only [smul_neg,neg_smul,neg_neg] using congrArg Neg.neg h₁)
    have hb : s = -b := smul_injective_scalar (primitive_rot hv)
      (by simpa only [rot_neg,smul_neg,neg_smul,neg_neg] using congrArg Neg.neg h₂)
    exact Or.inr (by simp [flip,ha,hb])

end RTS.Lifting
