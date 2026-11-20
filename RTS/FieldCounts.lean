module

public import RTS.FiniteCircle
public import Mathlib.Tactic

/-! The parametrized finite-field configurations of §2.1. -/

@[expose] public section

namespace RTS.FieldCounts
open Finset

variable {F : Type*} [Field F]
abbrev Plane (F : Type*) := F × F

def lengthSq (v : Plane F) := v.1^2 + v.2^2
def quarterTurn (v : Plane F) : Plane F := (-v.2, v.1)

def toBasis (x w : Plane F) : Plane F :=
  (w.1 * x.1 + w.2 * x.2, -w.1 * x.2 + w.2 * x.1)
def fromBasis (x z : Plane F) : Plane F :=
  (x.1 * z.1 - x.2 * z.2, x.2 * z.1 + x.1 * z.2)

def basisEquiv (x : UnitCircle F) : Plane F ≃ Plane F where
  toFun := toBasis x
  invFun := fromBasis x
  left_inv w := by
    have hx := x.property
    apply Prod.ext <;> dsimp [fromBasis,toBasis]
    · linear_combination w.1 * hx
    · linear_combination w.2 * hx
  right_inv z := by
    have hx := x.property
    apply Prod.ext <;> dsimp [fromBasis,toBasis]
    · linear_combination z.1 * hx
    · linear_combination z.2 * hx

theorem lengthSq_toBasis (x : UnitCircle F) (w : Plane F) :
    lengthSq (toBasis x w) = lengthSq w := by
  dsimp [toBasis, lengthSq]
  linear_combination (w.1^2+w.2^2) * x.property

@[simp] theorem basis_zero (x : UnitCircle F) : basisEquiv x 0 = 0 := by
  simp [basisEquiv, toBasis]

theorem toBasis_add (x u v : Plane F) :
    toBasis x (u+v) = toBasis x u + toBasis x v := by
  ext <;> simp [toBasis] <;> ring

theorem toBasis_smul (x v : Plane F) (r : F) :
    toBasis x (r • v) = r • toBasis x v := by
  ext <;> simp [toBasis] <;> ring

theorem toBasis_quarterTurn (x v : Plane F) :
    toBasis x (quarterTurn v) = quarterTurn (toBasis x v) := by
  ext <;> simp [toBasis, quarterTurn]; ring

theorem toBasis_center (x : UnitCircle F) :
    toBasis x.val x.val = ((1, 0) : Plane F) := by
  apply Prod.ext
  · dsimp [toBasis]
    simpa [sq] using x.property
  · dsimp [toBasis]; ring

/-- Four circle memberships for an ordered parameter tuple with first vertex x. -/
def RectAt (x w : Plane F) (r s : F) : Prop :=
  lengthSq x = 1 ∧ lengthSq (x + r • w) = 1 ∧
  lengthSq (x + s • quarterTurn w) = 1 ∧ lengthSq (x + r • w + s • quarterTurn w) = 1

def TriAt (x w : Plane F) (r s : F) : Prop :=
  lengthSq x = 1 ∧ lengthSq (x + r • w) = 1 ∧
  lengthSq (x + (2 : F)⁻¹ • (r • w + s • quarterTurn w)) = 1

def PinAt (k w : Plane F) (r s : F) : Prop :=
  lengthSq (k - (2 : F)⁻¹ • (r • w + s • quarterTurn w)) = 1 ∧
  lengthSq (k + (2 : F)⁻¹ • (r • w - s • quarterTurn w)) = 1

instance [DecidableEq F] (x w : Plane F) (r s : F) : Decidable (TriAt x w r s) := by
  unfold TriAt
  infer_instance

instance [DecidableEq F] (x w : Plane F) (r s : F) : Decidable (PinAt x w r s) := by
  unfold PinAt
  infer_instance

theorem rectAt_toBasis (x : UnitCircle F) (w : Plane F) (r s : F) :
    RectAt x w r s ↔ RectAt (1, 0) (basisEquiv x w) r s := by
  unfold RectAt
  simp only [basisEquiv, Equiv.coe_fn_mk, ← toBasis_center x, ← toBasis_smul,
    ← toBasis_quarterTurn, ← toBasis_add, lengthSq_toBasis]

theorem triAt_toBasis (x : UnitCircle F) (w : Plane F) (r s : F) :
    TriAt x w r s ↔ TriAt (1, 0) (basisEquiv x w) r s := by
  unfold TriAt
  simp only [basisEquiv, Equiv.coe_fn_mk, ← toBasis_center x, ← toBasis_smul,
    ← toBasis_quarterTurn, ← toBasis_add, lengthSq_toBasis]

theorem rectAt_origin_equations (w : Plane F) (r s : F) :
    RectAt (1,0) w r s ↔
    r * (2*w.1 + r*lengthSq w) = 0 ∧ s * (-2*w.2 + s*lengthSq w) = 0 := by
  simp [-mul_eq_zero, RectAt,lengthSq,quarterTurn,Prod.smul_fst,Prod.smul_snd]
  constructor
  · rintro ⟨h₁,h₂,_⟩
    constructor
    · linear_combination h₁
    · linear_combination h₂
  · rintro ⟨h₁,h₂⟩
    refine ⟨?_,?_,?_⟩
    · linear_combination h₁
    · linear_combination h₂
    · linear_combination h₁+h₂

theorem triAt_origin_equations (w : Plane F) (r s : F) (h₂ : (2 : F) ≠ 0) :
    TriAt (1,0) w r s ↔ r * (2*w.1+r*lengthSq w) = 0 ∧
      lengthSq w * (r^2+s^2) + 4*w.1*r - 4*w.2*s = 0 := by
  simp [-mul_eq_zero, TriAt,lengthSq,quarterTurn,Prod.smul_fst,Prod.smul_snd]
  constructor
  · rintro ⟨h₁,h₂'⟩
    constructor
    · linear_combination h₁
    · field_simp at h₂'
      linear_combination h₂'
  · rintro ⟨h₁,h₂'⟩
    constructor
    · linear_combination h₁
    · field_simp
      linear_combination h₂'

variable [Fintype F] [DecidableEq F]

noncomputable def rectChoices (x w : Plane F) : Finset (F × F) := by
  classical exact univ.filter fun v => RectAt x w v.1 v.2

noncomputable def triangleChoices (x w : Plane F) : Finset (F × F) := by
  classical exact univ.filter fun v => TriAt x w v.1 v.2

/-- This counts parameter tuples (x,w,r,s), including zero sides but excluding w=0. -/
noncomputable def rectangles (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℕ :=
  ∑ x : UnitCircle F, ∑ w ∈ (univ : Finset (Plane F)).erase 0, (rectChoices x w).card

noncomputable def triangles (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℕ :=
  ∑ x : UnitCircle F, ∑ w ∈ (univ : Finset (Plane F)).erase 0, (triangleChoices x w).card

theorem norm_ne_zero (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) {w : Plane (ZMod p)}
    (hw : w ≠ 0) : lengthSq w ≠ 0 := by
  intro h
  have hs : w.1 ^ 2 = -w.2 ^ 2 := eq_neg_of_add_eq_zero_left h
  by_cases h₂ : w.2 = 0
  · have h₁ : w.1 = 0 := by simpa [h₂] using hs
    exact hw (Prod.ext h₁ h₂)
  · exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' h₂ hs hp

omit [Fintype F] in
theorem pairRoots_card (x : F) : ({0,x} : Finset F).card = if x = 0 then 1 else 2 := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx, Ne.symm hx]

theorem rectChoices_origin_eq {w : Plane F} (hn : lengthSq w ≠ 0) :
    rectChoices (1,0) w = ({0, -(2*w.1) / lengthSq w} : Finset F) ×ˢ
      ({0, (2*w.2) / lengthSq w} : Finset F) := by
  classical
  ext ⟨r,s⟩
  simp only [rectChoices, mem_filter, mem_univ, true_and, rectAt_origin_equations,
    mul_eq_zero, mem_product, mem_insert, mem_singleton]
  apply and_congr <;> apply or_congr_right
  · rw [eq_div_iff hn]
    constructor <;> intro h <;> linear_combination h
  · rw [eq_div_iff hn]
    constructor <;> intro h <;> linear_combination h

def axisChoices (a : F) : ℕ := if a = 0 then 1 else 2

theorem rectChoices_origin_card {w : Plane F} (hn : lengthSq w ≠ 0) (h₂ : (2 : F) ≠ 0) :
    (rectChoices (1,0) w).card = axisChoices w.1 * axisChoices w.2 := by
  rw [rectChoices_origin_eq hn, card_product, pairRoots_card, pairRoots_card]
  simp [axisChoices, hn, h₂]

theorem sum_axisChoices : (∑ a : F, axisChoices a) = 2 * (Fintype.card F - 1) + 1 := by
  classical
  rw [← sum_erase_add _ _ (mem_univ (0 : F))]
  have hpos : ∀ x ∈ (univ : Finset F).erase 0, axisChoices x = 2 :=
    fun x hx => by simp [axisChoices, ne_of_mem_erase hx]
  rw [sum_congr rfl hpos]
  simp [axisChoices, Nat.mul_comm]

omit [DecidableEq F] in
theorem rectChoices_normalize (x : UnitCircle F) (w : Plane F) :
    rectChoices x w = rectChoices (1,0) (basisEquiv x w) := by
  classical
  ext ⟨r,s⟩
  simpa [rectChoices] using rectAt_toBasis x w r s

theorem triangleChoices_normalize (x : UnitCircle F) (w : Plane F) :
    triangleChoices x w = triangleChoices (1,0) (basisEquiv x w) := by
  classical
  ext ⟨r,s⟩
  simpa [triangleChoices] using triAt_toBasis x w r s

theorem sum_basis (x : UnitCircle F) (f : Plane F → ℕ) :
    (∑ w ∈ (univ : Finset (Plane F)).erase 0, f (basisEquiv x w)) =
      ∑ w ∈ (univ : Finset (Plane F)).erase 0, f w := by
  apply sum_equiv (basisEquiv x)
  · intro w
    simp only [mem_erase, mem_univ, and_true]
    apply not_congr
    simpa using ((basisEquiv x).injective.eq_iff (a := w) (b := 0)).symm
  · simp

theorem rectangles_card (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    rectangles (ZMod p) = 4*(p-1)*p*(p+1) := by
  classical
  have h₂ : (2 : ZMod p) ≠ 0 := by
    intro h
    apply norm_ne_zero p hp (w := (1,1)) (by simp)
    simpa [lengthSq, one_add_one_eq_two] using h
  have hone (x : UnitCircle (ZMod p)) :
      (∑ w ∈ (univ : Finset (Plane (ZMod p))).erase 0, (rectChoices x w).card) =
        4*(p-1)*p := by
    simp_rw [rectChoices_normalize x]
    rw [sum_basis x (fun w => (rectChoices (1,0) w).card)]
    have hlocal : (∑ w ∈ (univ : Finset (Plane (ZMod p))).erase 0,
        (rectChoices (1,0) w).card) = ∑ w ∈ (univ : Finset (Plane (ZMod p))).erase 0,
        axisChoices w.1 * axisChoices w.2 :=
      sum_congr rfl fun w hw => rectChoices_origin_card (norm_ne_zero p hp (ne_of_mem_erase hw)) h₂
    rw [hlocal]
    have hall := sum_erase_add (univ : Finset (Plane (ZMod p)))
      (fun w => axisChoices w.1 * axisChoices w.2) (mem_univ 0)
    rw [Fintype.sum_prod_type] at hall
    simp_rw [← mul_sum, ← sum_mul, sum_axisChoices, ZMod.card] at hall
    have hzero : axisChoices (0 : ZMod p) = 1 := by simp [axisChoices]
    change _ + axisChoices (0 : ZMod p) * axisChoices (0 : ZMod p) = _ at hall
    rw [hzero, one_mul] at hall
    have hp₀ := (Fact.out : Nat.Prime p).pos
    have hp' : p = (p-1)+1 := by omega
    have hmul : 4*(p-1)*p + 1 = (2*(p-1)+1)*(2*(p-1)+1) := by
      conv_lhs => arg 1; arg 2; rw [hp']
      ring
    omega
  unfold rectangles
  simp_rw [hone]
  simp [card_unitCircle p hp, Nat.mul_comm]

def roots (a : F) : Finset F := univ.filter fun u => u^2 = a

omit [Fintype F] [DecidableEq F] in
/-- Completion of the square in the nonzero-base branch of Lemma 2.2. -/
theorem triangle_second_root (w : Plane F) (s : F) (hn : lengthSq w ≠ 0) (h₂ : (2:F) ≠ 0) :
    lengthSq w * ((-(2*w.1)/lengthSq w)^2 + s^2)
      + 4*w.1*(-(2*w.1)/lengthSq w) - 4*w.2*s = 0 ↔
      ((lengthSq w)*s/2 - w.2)^2 = lengthSq w := by
  have h : lengthSq w = w.1^2+w.2^2 := rfl
  field_simp
  constructor <;> intro h'
  · linear_combination h' - 4 * h
  · linear_combination h' + 4 * h

def slopeEquiv (b n : F) (hn : n ≠ 0) (h₂ : (2:F) ≠ 0) : F ≃ F where
  toFun s := n*s/2-b
  invFun u := 2*(u+b)/n
  left_inv s := by field_simp; ring
  right_inv u := by field_simp; ring

theorem triangleChoices_origin_eq {w : Plane F} (hn : lengthSq w ≠ 0) (h₂ : (2:F) ≠ 0) :
    triangleChoices (1,0) w =
      ({0} : Finset F) ×ˢ {0, 4*w.2/lengthSq w} ∪
      (if w.1 = 0 then ∅ else
        ({-(2*w.1)/lengthSq w} : Finset F) ×ˢ
        (roots (lengthSq w)).map (slopeEquiv w.2 (lengthSq w) hn h₂).symm.toEmbedding) := by
  classical
  ext ⟨r,s⟩
  simp only [triangleChoices, mem_filter, mem_univ, true_and, triAt_origin_equations w r s h₂,
    mul_eq_zero, mem_union, mem_product, mem_singleton, mem_insert]
  have hr : 2 * w.1 + r * lengthSq w = 0 ↔ r = -(2*w.1)/lengthSq w := by
    rw [eq_div_iff hn]
    constructor <;> intro h <;> linear_combination h
  have hs : s * (s * lengthSq w - 4*w.2) = 0 ↔ s = 0 ∨ s = 4*w.2/lengthSq w := by
    rw [mul_eq_zero, eq_div_iff hn, sub_eq_zero]
  by_cases hr₀ : r = 0
  · subst r
    have h : lengthSq w * ((0:F)^2+s^2) + 4*w.1*0 - 4*w.2*s =
        s*(s*lengthSq w-4*w.2) := by ring
    rw [h,hs]
    by_cases ha : w.1 = 0 <;> simp [ha,hn,h₂]
  · rw [hr]
    by_cases ha : w.1 = 0
    · simp [ha,hr₀]
    · simp only [hr₀, ha, ite_false, false_or, false_and, mem_product, mem_singleton]
      apply and_congr_right
      intro hr'
      subst r
      rw [triangle_second_root w s hn h₂]
      constructor
      · intro h
        exact mem_map.mpr ⟨(slopeEquiv w.2 _ hn h₂) s, by simpa [roots, slopeEquiv] using h,
          (slopeEquiv w.2 _ hn h₂).symm_apply_apply s⟩
      · intro h
        obtain ⟨u,hu,hu'⟩ := mem_map.mp h
        have heu : (slopeEquiv w.2 _ hn h₂) s = u := by
          rw [← hu']; exact (slopeEquiv w.2 _ hn h₂).apply_symm_apply u
        rw [show lengthSq w * s / 2 - w.2 = u from heu]
        simpa [roots] using hu

theorem triangleChoices_origin_card {w : Plane F} (hn : lengthSq w ≠ 0) (h₂ : (2:F) ≠ 0) :
    (triangleChoices (1,0) w).card =
    axisChoices w.2 + (if w.1 = 0 then 0 else (roots (lengthSq w)).card) := by
  classical
  rw [triangleChoices_origin_eq hn h₂]
  have h₄ : (4 : F) ≠ 0 := by
    rw [show (4:F) = 2*2 by norm_num]
    exact mul_ne_zero h₂ h₂
  by_cases ha : w.1 = 0
  · simp only [ha, ite_true, union_empty, add_zero, card_product, card_singleton, one_mul, pairRoots_card]
    simp [h₄,hn,axisChoices]
  · simp only [ha, ite_false]
    rw [card_union_of_disjoint]
    · simp only [card_product, card_singleton, one_mul, card_map, pairRoots_card]
      simp [h₄,hn,axisChoices]
    · apply disjoint_left.mpr
      intro v h₁ h₃
      have hz := (mem_product.mp h₁).1
      have hnz := (mem_product.mp h₃).1
      simp only [mem_singleton] at hz hnz
      rw [hz] at hnz
      exact (div_ne_zero (neg_ne_zero.mpr (mul_ne_zero h₂ ha)) hn) hnz.symm

theorem sum_roots_sq_add_sq {a : F} (ha : a ≠ 0) (hF : ringChar F ≠ 2) (h₂ : (2 : F) ≠ 0) :
    (∑ b : F, (roots (a^2 + b^2)).card) = Fintype.card F - 1 := by
  classical
  have chr (x : F) : ((roots x).card : ℤ) = quadraticChar F x + 1 := by
    simpa [roots, Set.toFinset_ofPred] using quadraticChar_card_sqrts hF x
  have hsub (t : F) : quadraticChar F (a ^ 2 + (a*t)^2) = quadraticChar F (1+t^2) := by
    rw [show a^2+(a*t)^2=a^2*(1+t^2) by ring, map_mul, map_pow, quadraticChar_sq_one ha, one_mul]
  have hsum : (∑ b : F, quadraticChar F (a^2+b^2)) = -1 := by
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ a ha) (fun b => quadraticChar F (a^2+b^2))]
    simpa only [Equiv.mulLeft₀_apply, hsub] using quadraticChar_one_add_sq_sum hF h₂
  have hnat : ((∑ b : F, (roots (a^2+b^2)).card) : ℤ) =
      (Fintype.card F : ℤ)-1 := by
    simp_rw [chr]
    rw [sum_add_distrib, hsum]
    simp; ring
  have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
  have hcast : ((Fintype.card F - 1 : ℕ) : ℤ) = (Fintype.card F : ℤ)-1 := by
    exact_mod_cast Int.ofNat_sub hpos
  rw [← hcast] at hnat
  exact_mod_cast hnat

theorem triangles_card (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    triangles (ZMod p) = 3*(p-1)*p*(p+1) := by
  classical
  have h₂ : (2 : ZMod p) ≠ 0 := by
    intro h
    apply norm_ne_zero p hp (w := (1,1)) (by simp)
    simpa [lengthSq, one_add_one_eq_two] using h
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  let f (w : Plane (ZMod p)) :=
    axisChoices w.2 + (if w.1 = 0 then 0 else (roots (lengthSq w)).card)
  have h₀ : f 0 = 1 := by simp [f, axisChoices]
  have row (a : ZMod p) : (∑ b : ZMod p, f (a,b)) =
      (2*(p-1)+1) + (if a = 0 then 0 else p-1) := by
    dsimp [f]
    rw [sum_add_distrib, sum_axisChoices, ZMod.card]
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha, lengthSq, sum_roots_sq_add_sq ha hF h₂]
  have allrows : (∑ w : Plane (ZMod p), f w) =
      p*(2*(p-1)+1)+(p-1)*(p-1) := by
    rw [Fintype.sum_prod_type]
    simp_rw [row]
    rw [sum_add_distrib]
    congr 1
    · simp
    · rw [← sum_erase_add _ _ (mem_univ (0 : ZMod p))]
      have hh : ∀ a ∈ (univ : Finset (ZMod p)).erase 0,
          (if a = 0 then 0 else p-1) = p-1 := fun a ha => by simp [ne_of_mem_erase ha]
      rw [sum_congr rfl hh]
      simp
  have hone (x : UnitCircle (ZMod p)) :
      (∑ w ∈ (univ : Finset (Plane (ZMod p))).erase 0, (triangleChoices x w).card) =
      3*(p-1)*p := by
    simp_rw [triangleChoices_normalize x]
    rw [sum_basis x (fun w => (triangleChoices (1,0) w).card)]
    have hlocal : (∑ w ∈ (univ : Finset (Plane (ZMod p))).erase 0,
        (triangleChoices (1,0) w).card) = ∑ w ∈ (univ : Finset (Plane (ZMod p))).erase 0,
        f w := sum_congr rfl fun w hw =>
      triangleChoices_origin_card (norm_ne_zero p hp (ne_of_mem_erase hw)) h₂
    rw [hlocal]
    have hall := sum_erase_add (univ : Finset (Plane (ZMod p))) f (mem_univ 0)
    rw [h₀, allrows] at hall
    have hp₀ := (Fact.out : Nat.Prime p).pos
    have hp' : p = (p-1)+1 := by omega
    have hmul : 3*(p-1)*p + 1 = p*(2*(p-1)+1)+(p-1)*(p-1) := by
      conv_lhs => arg 1; arg 2; rw [hp']
      conv_rhs => arg 1; arg 1; rw [hp']
      ring
    omega
  unfold triangles
  simp_rw [hone]
  simp [card_unitCircle p hp, Nat.mul_comm]

section Pinned

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def pinChoices (k w : Plane F) : Finset (F × F) := by
  classical exact univ.filter fun v => PinAt k w v.1 v.2

noncomputable def pinnedTriangles (k : Plane F) : ℕ :=
  ∑ w ∈ (univ : Finset (Plane F)).erase 0, (pinChoices k w).card

omit [Fintype F] [DecidableEq F] in
theorem toBasis_sub (x u v : Plane F) :
    toBasis x (u-v) = toBasis x u - toBasis x v := by
  ext <;> simp [toBasis] <;> ring

omit [Fintype F] [DecidableEq F] in
theorem pinAt_toBasis (k : UnitCircle F) (w : Plane F) (r s : F) :
    PinAt k w r s ↔ PinAt (1,0) (basisEquiv k w) r s := by
  unfold PinAt
  simp only [basisEquiv, Equiv.coe_fn_mk, ← toBasis_center k, ← toBasis_smul,
    ← toBasis_quarterTurn, ← toBasis_sub, ← toBasis_add, lengthSq_toBasis]

theorem pinnedTriangles_constant (k : UnitCircle F) :
    pinnedTriangles (k : Plane F) = pinnedTriangles ((1,0) : Plane F) := by
  classical
  have h (w : Plane F) : pinChoices k w = pinChoices (1,0) (basisEquiv k w) := by
    ext ⟨r,s⟩
    simpa [pinChoices] using pinAt_toBasis k w r s
  unfold pinnedTriangles
  simp_rw [h]
  exact sum_basis k (fun w => (pinChoices (1,0) w).card)

def apexOffset (w : Plane F) (r s : F) := (2:F)⁻¹ • (r • w + s • quarterTurn w)

omit [Fintype F] [DecidableEq F] in
theorem secondBase (k w : Plane F) (r s : F) (h₂ : (2:F) ≠ 0) :
    k - apexOffset w r s + r • w = k + (2:F)⁻¹ • (r • w - s • quarterTurn w) := by
  ext <;> simp [apexOffset, quarterTurn] <;> field_simp <;> ring

omit [Fintype F] [DecidableEq F] in
theorem triAt_of_pinAt {k w : Plane F} {r s : F} (hk : lengthSq k = 1)
    (h : PinAt k w r s) (h₂ : (2:F) ≠ 0) : TriAt (k - apexOffset w r s) w r s := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [secondBase k w r s h₂]
    exact h.2
  · change lengthSq (k-apexOffset w r s + apexOffset w r s) = 1
    simpa using hk

omit [Fintype F] [DecidableEq F] in
theorem pinAt_of_triAt {x w : Plane F} {r s : F} (h : TriAt x w r s) (h₂ : (2:F) ≠ 0) :
    PinAt (x + apexOffset w r s) w r s := by
  refine ⟨?_, ?_⟩
  · change lengthSq (x+apexOffset w r s - apexOffset w r s) = 1
    simpa using h.1
  · rw [← secondBase _ _ _ _ h₂, add_sub_cancel_right]
    exact h.2.1

theorem apex_fiber_count (w : Plane F) (r s : F) (h₂ : (2:F) ≠ 0) :
    (∑ x : UnitCircle F, if TriAt x w r s then 1 else 0) =
      ∑ k : UnitCircle F, if PinAt k w r s then (1:ℕ) else 0 := by
  classical
  rw [← card_filter, ← card_filter]
  refine card_bij' (fun x hx => ⟨x.val + apexOffset w r s, (mem_filter.mp hx).2.2.2⟩)
    (fun k hk => ⟨k.val - apexOffset w r s, (mem_filter.mp hk).2.1⟩) ?_ ?_ ?_ ?_
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _, pinAt_of_triAt (mem_filter.mp hx).2 h₂⟩
  · intro k hk
    exact mem_filter.mpr ⟨mem_univ _, triAt_of_pinAt k.property (mem_filter.mp hk).2 h₂⟩
  · intro x hx
    exact Subtype.ext (add_sub_cancel_right ..)
  · intro k hk
    exact Subtype.ext (sub_add_cancel ..)

theorem triangles_sum_pins (h₂ : (2:F) ≠ 0) :
    triangles F = ∑ k : UnitCircle F, pinnedTriangles (k : Plane F) := by
  classical
  unfold triangles pinnedTriangles triangleChoices pinChoices
  simp_rw [card_filter]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro w _
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  rintro ⟨r,s⟩ _
  exact apex_fiber_count w r s h₂

theorem pinnedTriangles_card (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (k : UnitCircle (ZMod p)) :
    pinnedTriangles (k : Plane (ZMod p)) = 3*(p-1)*p := by
  classical
  have h₂ : (2 : ZMod p) ≠ 0 := by
    intro h
    apply norm_ne_zero p hp (w := (1,1)) (by simp)
    simpa [lengthSq, one_add_one_eq_two] using h
  have hc := triangles_sum_pins h₂
  simp_rw [pinnedTriangles_constant] at hc
  simp only [triangles_card p hp, sum_const, card_univ, card_unitCircle p hp, nsmul_eq_mul] at hc
  rw [pinnedTriangles_constant]
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p+1) (by simpa [Nat.mul_comm] using hc.symm)

end Pinned

end RTS.FieldCounts
