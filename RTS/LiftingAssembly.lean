module

public import RTS.CircleLift
public import RTS.CRTMembership
public import RTS.LiftingResidues
public import RTS.LiftingBounds
public import RTS.LiftingTuples
public import Mathlib.Data.Nat.GCD.BigOperators

/-! Assembly of the uniform rectangle and pinned triangle estimates in §2.3. -/
@[expose] public noncomputable section

namespace RTS
open Finset Real
open CRT Lifting

namespace CRT.PrimeSet

theorem modulus_pos (P : PrimeSet) : 0 < P.modulus :=
  Finset.prod_pos fun p _ => (P.prime p p.property).pos

theorem direction_coprime (P : PrimeSet) {w : P.Pt} (hw : P.goodDirection w) :
    (Nat.gcd (w 0).val (w 1).val).Coprime P.modulus := by
  have : NeZero P.modulus := ⟨P.modulus_pos.ne'⟩
  apply Nat.coprime_prod_right_iff.mpr
  intro p _
  apply Nat.Coprime.symm
  apply (P.prime p p.property).coprime_iff_not_dvd.mpr
  intro h
  apply hw p
  have coord (i : Fin 2) (hi : (p:ℕ) ∣ (w i).val) : P.scalarEquiv (w i) p = 0 := by
    calc
      _ = P.scalarEquiv (((w i).val : ℕ) : P.R) p := by rw [ZMod.natCast_zmod_val]
      _ = ((w i).val : P.Local p) := congrFun (map_natCast P.scalarEquiv (w i).val) p
      _ = 0 := (ZMod.natCast_eq_zero_iff (w i).val p).mpr hi
  exact Prod.ext (coord 0 (h.trans (Nat.gcd_dvd_left ..)))
    (coord 1 (h.trans (Nat.gcd_dvd_right ..)))

theorem admissible_rectangle_residue (P : PrimeSet) (v) (hv : v ∈ P.rects) :
    (Nat.gcd (v.2.1 0).val (v.2.1 1).val).Coprime P.modulus := by
  exact P.direction_coprime ((P.rects_iff v.1 v.2.1 v.2.2.1 v.2.2.2).mp hv).1

theorem reduction_in_circle (P : PrimeSet) (k : Point) :
    reduce P.modulus k ∈ P.circle ↔ Int.ModEq P.modulus (dot₂ k k) 1 := by
  rw [P.circle_iff, ← ZMod.intCast_eq_intCast_iff]
  simp [reduce,dot₂,Fin.sum_univ_two,sq]

theorem circleLift_as_residue_union (P : PrimeSet) (N : ℕ) :
    circleLift P.modulus N = liftedSet P.modulus P.circle N := by
  ext k
  rw [mem_circleLift, mem_liftedSet P.modulus_pos, P.reduction_in_circle]
  apply and_congr_left
  intro _
  apply forall_congr'
  intro i
  rw [abs_le]
  norm_cast

theorem circleLift_size_upper (P : PrimeSet) (N : ℕ) (h : P.modulus ≤ N) :
    ((circleLift P.modulus N).card : ℝ) ≤ 9 * P.circle.card * (N:ℝ)^2/(P.modulus:ℝ)^2 := by
  have hq : (0 : ℝ) < P.modulus := by exact_mod_cast P.modulus_pos
  have hN : (P.modulus:ℝ) ≤ N := by exact_mod_cast h
  have he := (abs_le.mp (liftedSet_card_error P.modulus_pos P.circle hN)).2
  rw [← circleLift_as_residue_union] at he
  have hratio : 1 ≤ (N:ℝ)/P.modulus := (one_le_div hq).mpr hN
  have hcoef : 5*(P.circle.card:ℝ)*N/P.modulus ≤
      5*P.circle.card*(N:ℝ)^2/(P.modulus:ℝ)^2 := by
    calc
      _ = 5*P.circle.card*((N:ℝ)/P.modulus)*1 := by ring
      _ ≤ 5*P.circle.card*((N:ℝ)/P.modulus)*((N:ℝ)/P.modulus) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hsum : 4*(P.circle.card:ℝ)*N^2/(P.modulus:ℝ)^2 + 5*P.circle.card*N^2/(P.modulus:ℝ)^2 =
      9*P.circle.card*N^2/(P.modulus:ℝ)^2 := by ring
  linarith only [he,hcoef,hsum]

end CRT.PrimeSet

/-- The scale for one modular pinned parameter class after lifting. -/
def pinScale (q N : ℕ) : ℝ := (N:ℝ)^2 * log N / (q:ℝ)^4

theorem pinScale_one_le {C : ℝ} (hC : 1 ≤ C) {q N : ℕ} (hq : 0 < q)
    (he : exp (C*(q:ℝ)^2) ≤ N) : 1 ≤ pinScale q N := by
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hs : (q:ℝ)^2 ≤ C*(q:ℝ)^2 := le_mul_of_one_le_left (sq_nonneg _) hC
  have hN : (q:ℝ)^2 ≤ N := hs.trans ((Real.add_one_le_exp _).trans' (by linarith) |>.trans he)
  have hNpos : (0:ℝ) < N := (exp_pos _).trans_le he
  have hlog : C*(q:ℝ)^2 ≤ log N := (le_log_iff_exp_le hNpos).mpr he
  have hsq : (1:ℝ) ≤ (q:ℝ)^2 := one_le_pow₀ hq₁
  unfold pinScale
  apply (le_div_iff₀ (by positivity : (0:ℝ) < (q:ℝ)^4)).mpr
  calc
    1 * (q:ℝ)^4 = ((q:ℝ)^2)^2 * 1 := by ring
    _ ≤ (N:ℝ)^2 * log N := mul_le_mul (by gcongr) (hsq.trans (hs.trans hlog))
      zero_le_one (sq_nonneg _)

/-- The tuple bounds for one modulus have absolute coefficients c,D and one
absolute exponential threshold C. The result retains the modular factor (4/3)^m. -/
theorem uniformLiftBounds_of_counts (P : PrimeSet) {c D C : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hC : 1 ≤ C)
    (hrect : ∀ N : ℕ, exp (C*(P.modulus:ℝ)^2) ≤ N →
      c * P.rects.card / (P.modulus:ℝ)^6 * liftScale N ≤ rectangleCount (circleLift P.modulus N))
    (hpin : ∀ N : ℕ, exp (C*(P.modulus:ℝ)^2) ≤ N → ∀ k ∈ circleLift P.modulus N,
      (pinnedTriangleCount (circleLift P.modulus N) k : ℝ) ≤
        D * (P.pins (reduce P.modulus k)).card * pinScale P.modulus N + 1) :
    UniformLiftBounds (circleLift P.modulus) C
      (c/(9*(D+1)) * (4/3:ℝ)^P.primes.card) P.modulus := by
  let q := P.modulus
  let B : ℝ := P.circle.card
  let S : ℝ := (P.circle.sup fun k => (P.pins k).card : ℕ)
  have hq : 0 < q := P.modulus_pos
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hS₀ : 0 < S := by
    dsimp [S]
    rw [P.max_pins_card]
    exact_mod_cast Finset.prod_pos (fun p _ => by
      have hp := (P.prime p p.property).two_le
      have : 0 < (p:ℕ)-1 := by omega
      positivity)
  have hS : 1 ≤ S := by
    dsimp [S] at *
    exact_mod_cast (show 1 ≤ P.circle.sup (fun k => (P.pins k).card) by exact_mod_cast hS₀)
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Finset.card_pos.mpr P.circle_nonempty
  have hratio : (P.rects.card : ℝ) / (B*S) = (4/3:ℝ)^P.primes.card := by
    simpa [B,S] using P.rect_max_pin_ratio
  have hR : (4/3:ℝ)^P.primes.card * (B*S) = P.rects.card :=
    (div_eq_iff (mul_pos hB hS₀).ne').mp hratio |>.symm
  refine ⟨9*(D+1)*B*S/(q:ℝ)^6, by positivity, ?_⟩
  intro N he
  have hN : q ≤ N := by
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
    have h₁ : (q:ℝ) ≤ (q:ℝ)^2 := by nlinarith
    have h₂ : (q:ℝ)^2 ≤ C*(q:ℝ)^2 := le_mul_of_one_le_left (sq_nonneg _) hC
    exact_mod_cast h₁.trans (h₂.trans ((Real.add_one_le_exp _).trans' (by linarith) |>.trans he))
  have hscale := pinScale_one_le hC hq he
  have hpinTotal : (maxPinnedCount (circleLift q N) : ℝ) ≤ (D+1)*S*pinScale q N := by
    by_cases hA : (circleLift q N).Nonempty
    · obtain ⟨k,hk,hk'⟩ := Finset.exists_mem_eq_sup _ hA (pinnedTriangleCount (circleLift q N))
      rw [maxPinnedCount,hk']
      have hkmod := (P.reduction_in_circle k).mpr (mem_circleLift.mp hk).2
      have hs : ((P.pins (reduce q k)).card : ℝ) ≤ S := by
        dsimp [q,S]
        exact_mod_cast (Finset.le_sup (f := fun b => (P.pins b).card) hkmod)
      calc
        _ ≤ D * (P.pins (reduce q k)).card * pinScale q N + 1 := hpin N he k hk
        _ ≤ D*S*pinScale q N + S*pinScale q N :=
          add_le_add (by gcongr) (one_le_mul_of_one_le_of_one_le hS hscale)
        _ = _ := by ring
    · have hA' := Finset.not_nonempty_iff_eq_empty.mp hA
      simp [hA',maxPinnedCount]
      positivity
  constructor
  · calc
      _ = c/(q:ℝ)^6 * ((4/3:ℝ)^P.primes.card * (B*S)) * liftScale N := by
        field_simp [show D+1 ≠ 0 by linarith]
      _ = _ := by rw [hR]; ring
      _ ≤ _ := hrect N he
  · rw [Nat.cast_mul]
    calc
      _ ≤ (9*B*(N:ℝ)^2/(q:ℝ)^2) * ((D+1)*S*pinScale q N) :=
        mul_le_mul (P.circleLift_size_upper N hN) hpinTotal (Nat.cast_nonneg _)
          (by positivity)
      _ = _ := by unfold pinScale liftScale; ring

/-- Assemble bounds on the finite parameter sets with the two geometric multiplicities.
The single exceptional pinned triangle at (k,k,k) contributes the additive one. -/
theorem uniformLiftBounds_of_tuples (P : PrimeSet) {c D C : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hC : 1 ≤ C)
    (hrect : ∀ N : ℕ, exp (C*(P.modulus:ℝ)^2) ≤ N →
      c * P.rects.card / (P.modulus:ℝ)^6 * liftScale N ≤
        (rectTupleSet P.modulus P.rects N).card)
    (hpin : ∀ (N : ℕ), exp (C*(P.modulus:ℝ)^2) ≤ N → ∀ b : P.Pt,
      ((pinTupleSet P.modulus (P.pins b) N).card : ℝ) ≤
        D * (P.pins b).card * pinScale P.modulus N)
    (hgeomR : ∀ N : ℕ, (rectTupleSet P.modulus P.rects N).card ≤
        2 * rectangleCount (circleLift P.modulus N))
    (hgeomP : ∀ (N : ℕ) (k : Point), k ∈ circleLift P.modulus N →
      pinnedTriangleCount (circleLift P.modulus N) k ≤
        (pinTupleSet P.modulus (P.pins (reduce P.modulus k)) N).card + 1) :
    UniformLiftBounds (circleLift P.modulus) C
      ((c/2)/(9*(D+1)) * (4/3:ℝ)^P.primes.card) P.modulus := by
  apply uniformLiftBounds_of_counts P (c := c/2) (D := D) (C := C) (by positivity) hD hC
  · intro N he
    have hr := hrect N he
    have hg : ((rectTupleSet P.modulus P.rects N).card : ℝ) ≤
        2 * rectangleCount (circleLift P.modulus N) := by exact_mod_cast hgeomR N
    calc
      _ = (c * P.rects.card / (P.modulus:ℝ)^6 * liftScale N)/2 := by ring
      _ ≤ _ := by linarith
  · intro N he k hk
    have hg : (pinnedTriangleCount (circleLift P.modulus N) k : ℝ) ≤
        ((pinTupleSet P.modulus (P.pins (reduce P.modulus k)) N).card : ℝ) + 1 := by
      exact_mod_cast hgeomP N k hk
    exact hg.trans (add_le_add (hpin N he (reduce P.modulus k)) le_rfl)

end RTS
