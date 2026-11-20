module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! The local unit circle used in the proof of Lemma 2.2. -/

@[expose] public section

namespace RTS

section Field

variable {F : Type*} [Field F]

abbrev UnitCircle (F : Type*) [Field F] := {x : F × F // x.1 ^ 2 + x.2 ^ 2 = 1}

def circleX (t : F) := (1 - t ^ 2) / (1 + t ^ 2)
def circleY (t : F) := (2 * t) / (1 + t ^ 2)

theorem circle_mem (t : F) (ht : 1 + t ^ 2 ≠ 0) :
    circleX t ^ 2 + circleY t ^ 2 = 1 := by
  unfold circleX circleY
  field_simp
  ring

theorem one_add_circleX (t : F) (ht : 1 + t ^ 2 ≠ 0) :
    1 + circleX t = 2 / (1 + t ^ 2) := by
  unfold circleX
  field_simp
  ring

/-- Rational parametrization plus the point (-1,0). The inverse is the slope b/(1+a). -/
def unitCircleEquiv [DecidableEq F] (h₂ : (2 : F) ≠ 0) (hd : ∀ t : F, 1 + t^2 ≠ 0) :
    Option F ≃ UnitCircle F where
  toFun
    | none => ⟨(-1, 0), by simp⟩
    | some t => ⟨(circleX t, circleY t), circle_mem t (hd t)⟩
  invFun x := if x.val.1 = -1 then none else some (x.val.2 / (1 + x.val.1))
  left_inv
    | none => by simp
    | some t => by
        have hx : circleX t ≠ -1 := by
          intro hx
          have hh := one_add_circleX t (hd t)
          rw [hx, add_neg_cancel] at hh
          exact div_ne_zero h₂ (hd t) hh.symm
        simp only [hx, ite_false, Option.some.injEq]
        rw [one_add_circleX t (hd t)]
        unfold circleY
        field_simp [hd t]
  right_inv := by
    rintro ⟨⟨a,b⟩, hab⟩
    change a^2 + b^2 = 1 at hab
    by_cases ha : a = -1
    · subst a
      have hb : b^2 = 0 := by simpa using hab
      have hb₀ : b = 0 := by simpa using hb
      simp [hb₀]
    · have hden : 1 + a ≠ 0 := by
        intro h
        apply ha
        linear_combination h
      have hden' := hd (b / (1+a))
      apply Subtype.ext
      simp only [ha, ite_false]
      apply Prod.ext
      · change circleX (b / (1+a)) = a
        unfold circleX
        apply (div_eq_iff hden').mpr
        field_simp
        linear_combination -(1+a) * hab
      · change circleY (b / (1+a)) = b
        unfold circleY
        apply (div_eq_iff hden').mpr
        field_simp
        linear_combination -b * hab

end Field

/-- Cardinality of the circle over F_p for every prime congruent to 3 modulo 4.
Uses mathlib's criterion for -1 to be a square in ZMod p. -/
theorem card_unitCircle (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    Fintype.card (UnitCircle (ZMod p)) = p + 1 := by
  have hd (t : ZMod p) : 1 + t^2 ≠ 0 := by
    intro h
    apply ZMod.mod_four_ne_three_of_sq_eq_neg_one (y := t) _ hp
    linear_combination h
  have h₂ : (2 : ZMod p) ≠ 0 := by
    intro h
    apply hd 1
    simpa [one_add_one_eq_two] using h
  rw [← Fintype.card_congr (unitCircleEquiv h₂ hd)]
  simp


section Hyperbola

variable {F : Type*} [Field F]

/-- Change variables from a point on u²−t²=1 to the unit u−t with inverse u+t. -/
def hyperbolaEquiv (h₂ : (2 : F) ≠ 0) :
    (Σ t : F, {u : F // u^2 = 1 + t^2}) ≃ Fˣ where
  toFun x := {
    val := x.2.val - x.1
    inv := x.2.val + x.1
    val_inv := by linear_combination x.2.property
    inv_val := by linear_combination x.2.property }
  invFun z := ⟨((↑z⁻¹ : F) - z) / 2,
    ⟨((z : F) + ↑z⁻¹) / 2, by
      field_simp
      have hz : (z : F) * ↑z⁻¹ = 1 := z.mul_inv
      linear_combination 4 * hz⟩⟩
  left_inv := by
    rintro ⟨t, ⟨u, h⟩⟩
    dsimp
    have ht : (u + t - (u - t)) / 2 = t := by field_simp; ring
    have hu : (u - t + (u + t)) / 2 = u := by field_simp; ring
    apply Sigma.ext ht
    apply (Subtype.heq_iff_coe_eq (fun x => by change (x^2 = 1 + ((u+t-(u-t)) / 2)^2) ↔ x^2 = 1+t^2; rw [ht])).2
    exact hu
  right_inv z := by
    apply Units.ext
    change ((z : F) + ↑z⁻¹) / 2 - ((↑z⁻¹ : F) - z) / 2 = z
    field_simp
    ring

/-- The quadratic character identity in the triangle count of Lemma 2.2.
The square-root fibers are counted by mathlib's quadraticChar_card_sqrts. -/
theorem quadraticChar_one_add_sq_sum [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (h₂ : (2 : F) ≠ 0) : ∑ t : F, quadraticChar F (1 + t^2) = -1 := by
  classical
  have hcard := Fintype.card_congr (hyperbolaEquiv h₂)
  rw [Fintype.card_sigma] at hcard
  have htotal : (∑ t : F, ((Fintype.card {u : F // u^2 = 1 + t^2} : ℕ) : ℤ)) =
      Fintype.card Fˣ := by exact_mod_cast hcard
  have hf (t : F) : ((Fintype.card {u : F // u^2 = 1 + t^2} : ℕ) : ℤ) =
      quadraticChar F (1 + t^2) + 1 := by
    rw [Fintype.card_subtype]
    simpa [Set.toFinset_ofPred] using quadraticChar_card_sqrts hF (1 + t^2)
  simp_rw [hf] at htotal
  rw [Finset.sum_add_distrib] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at htotal
  have hunits : (Fintype.card F : ℤ) = Fintype.card Fˣ + 1 := by
    exact_mod_cast Fintype.card_eq_card_units_add_one (α := F)
  omega

end Hyperbola

end RTS
