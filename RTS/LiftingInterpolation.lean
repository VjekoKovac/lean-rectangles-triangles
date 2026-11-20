module

public import RTS.GrowthReduction
public import RTS.LiftingBounds
public import RTS.CircleLift
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The every-cardinality interpolation of §2.3. Adjacent nested lattice sets
supply a rectangle numerator from below and a pinned denominator from above. -/
@[expose] public noncomputable section

namespace RTS

open Finset Real

theorem liftScale_pos {t : ℕ} (ht : 2 ≤ t) : 0 < liftScale t := by
  have ht' : 1 < (t:ℝ) := by exact_mod_cast (show 1 < t by omega)
  exact mul_pos (pow_pos (by positivity) _) (log_pos ht')

theorem liftScale_succ {t : ℕ} (ht : 2 ≤ t) : liftScale (t+1) ≤ 32 * liftScale t := by
  have ht' : 2 ≤ (t:ℝ) := by exact_mod_cast ht
  have hind : (t:ℝ)+1 ≤ 2*t := by linarith
  have hlog : log ((t:ℝ)+1) ≤ 2*log t := by
    calc log ((t:ℝ)+1) ≤ log (2*t) := log_le_log (by positivity) hind
         _ = log 2 + log t := log_mul (by norm_num) (by positivity)
         _ ≤ _ := by linarith only [log_le_log (by norm_num : (0 : ℝ) < 2) ht']
  simp only [liftScale, Nat.cast_add, Nat.cast_one]
  calc ((t:ℝ)+1)^4 * log ((t:ℝ)+1) ≤ (2*t)^4 * (2*log t) := by
         gcongr
         exact log_nonneg (by linarith)
       _ = _ := by ring

/-- A nested, unbounded family has consecutive members enclosing an n-point
set. The search starts at R, keeping the radius in the uniform-estimate range. -/
theorem exists_intermediate_exact {α : Type*} {A : ℕ → Finset α}
    (hmono : Monotone A) (hunb : ∀ n, ∃ t, n ≤ (A t).card) {R n : ℕ}
    (hR : (A R).card ≤ n) :
    ∃ t ≥ R, ∃ B : Finset α, A t ⊆ B ∧ B ⊆ A (t+1) ∧ B.card = n := by
  classical
  obtain ⟨s,hs⟩ := hunb (n+1)
  have hex : ∃ j, n < (A (R+j)).card := ⟨s, lt_of_lt_of_le (by omega : n < (A s).card)
    (card_le_card (hmono (by omega)))⟩
  let j := Nat.find hex
  have hj : n < (A (R+j)).card := Nat.find_spec hex
  have h0 : j ≠ 0 := by intro he; simp [he] at hj; omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have hbefore : ¬ n < (A (R+k)).card := Nat.find_min hex (show k < j by omega)
  have hafter : n ≤ (A (R+k+1)).card := by simpa only [hk,Nat.add_succ] using hj.le
  obtain ⟨B,h₁,h₂,h₃⟩ := exists_subsuperset_card_eq (hmono (by omega : R+k ≤ R+k+1))
    (le_of_not_gt hbefore) hafter
  exact ⟨R+k,by omega,B,h₁,h₂,h₃⟩

theorem pinnedRatio_ge {A : Finset Point} {r : ℝ} (hA : A.Nonempty)
    (h : r * ((A.card * maxPinnedCount A : ℕ) : ℝ) ≤ rectangleCount A) :
    r ≤ pinnedRatio A := by
  have hc := card_pos.mpr hA
  obtain ⟨k,hk⟩ := hA
  have hp := (card_le_pinnedTriangleCount A k).trans (le_sup (f := pinnedTriangleCount A) hk)
  have hd : (0:ℝ) < (A.card * maxPinnedCount A : ℕ) := by
    exact_mod_cast (Nat.mul_pos hc (hc.trans_le hp))
  exact (le_div_iff₀ hd).mpr h

/-- For all n beyond the initial bounding square, interpolate using adjacent
counts. This loses only the absolute factor 32 from the change of radius. -/
theorem exact_size_of_uniform_lift {A : ℕ → Finset Point} {q R n : ℕ} {C target : ℝ}
    (h : UniformLiftBounds A C target q) (hr : 0 ≤ target)
    (hmono : Monotone A) (hunb : ∀ n, ∃ t, n ≤ (A t).card)
    (hrect : ∀ {B D : Finset Point}, B ⊆ D → rectangleCount B ≤ rectangleCount D)
    (hpin : ∀ {B D : Finset Point}, B ⊆ D → maxPinnedCount B ≤ maxPinnedCount D)
    (hR : exp (C*(q:ℝ)^2) ≤ R) (hR₂ : 2 ≤ R) (hn : 0 < n) (hstart : (A R).card ≤ n) :
    ∃ B : Finset Point, B.card = n ∧ target / 32 ≤ pinnedRatio B := by
  obtain ⟨b,hb,h⟩ := h
  obtain ⟨t,ht,B,hsub₁,hsub₂,hcard⟩ := exists_intermediate_exact hmono hunb hstart
  have ht₂ := hR₂.trans ht
  have he : exp (C*(q:ℝ)^2) ≤ t := hR.trans (by exact_mod_cast ht)
  have he' := he.trans (by exact_mod_cast Nat.le_succ t : (t:ℝ) ≤ ↑(t+1))
  have hu := (h (t+1) he').2
  have hl := (h t he).1
  have hd : ((B.card * maxPinnedCount B : ℕ) : ℝ) ≤
      (((A (t+1)).card * maxPinnedCount (A (t+1)) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_le_mul (card_le_card hsub₂) (hpin hsub₂))
  refine ⟨B,hcard,pinnedRatio_ge (card_pos.mp (by omega)) ?_⟩
  calc _ ≤ (target/32) * (b * liftScale (t+1)) :=
         mul_le_mul_of_nonneg_left (hd.trans hu) (by positivity)
       _ ≤ (target/32) * (b * (32 * liftScale t)) := by
         gcongr
         exact liftScale_succ ht₂
       _ = target * b * liftScale t := by ring
       _ ≤ _ := hl.trans (by exact_mod_cast hrect hsub₁)

/-- One radius valid for both the real-box and the exact-size estimates.
Its bounding square fits below the double-exponential threshold. -/
theorem exists_lift_window {D C : ℝ} (hD : 1 ≤ D) (hC : 1 ≤ C) {q m : ℕ}
    (hq : 0 < q) (hm : 2 ≤ m) (hprod : (q:ℝ) ≤ exp (D*m*log m)) :
    ∃ R : ℕ, 2 ≤ R ∧ exp (C*(q:ℝ)^2) ≤ R ∧
      (2*(R:ℝ)+1)^2 ≤ exp (exp ((10+2*C+2*D)*m*log m)) := by
  let s := (m:ℝ) * log m
  have hm₂ : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hs : 1 ≤ s := by
    have hlog := (Real.log_two_gt_d9.le.trans (log_le_log (by norm_num) hm₂))
    dsimp [s]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm₂) (by linarith : 0 ≤ log (m:ℝ))]
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hX : 1 ≤ C*(q:ℝ)^2 := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hq₁)
  let X := C*(q:ℝ)^2
  let R := ⌈exp X⌉₊
  have hR : exp X ≤ (R:ℝ) := Nat.le_ceil _
  have hR' : (R:ℝ) ≤ exp X+1 := (Nat.ceil_lt_add_one (exp_pos X).le).le
  have hX' : 2 ≤ exp X := by linarith only [hX, add_one_le_exp X]
  have hR₂ : 2 ≤ R := by exact_mod_cast hX'.trans hR
  have hE : 1 ≤ exp (2*D*s) := one_le_exp (by positivity)
  have hq' : (q:ℝ)^2 ≤ exp (2*D*s) := by
    have hr := pow_le_pow_left₀ (by positivity : 0 ≤ (q:ℝ)) hprod 2
    convert hr using 1
    rw [← Real.exp_nat_mul]
    norm_cast
    dsimp [s]
    ring_nf
  have hfactor : 10+2*C ≤ exp ((10+2*C)*s) := by
    have := add_one_le_exp ((10+2*C)*s)
    nlinarith [mul_nonneg (by linarith : 0 ≤ 10+2*C) (sub_nonneg.mpr hs)]
  have hex : 2*(5+X) ≤ exp ((10+2*C+2*D)*m*log m) := by
    calc 2*(5+X) ≤ (10+2*C)*exp (2*D*s) := by
           dsimp [X]
           nlinarith [mul_le_mul_of_nonneg_left hq' (by linarith : 0 ≤ 2*C)]
         _ ≤ exp ((10+2*C)*s) * exp (2*D*s) :=
           mul_le_mul_of_nonneg_right hfactor (exp_pos _).le
         _ = _ := by rw [←exp_add]; congr 1; dsimp [s]; ring
  refine ⟨R,hR₂,hR,?_⟩
  calc (2*(R:ℝ)+1)^2 ≤ (5*exp X)^2 := by gcongr; linarith
       _ ≤ (exp 5 * exp X)^2 := by
         gcongr
         linarith only [add_one_le_exp 5]
       _ = exp (2*(5+X)) := by rw [←exp_add, ←Real.exp_nat_mul]; norm_num
       _ ≤ _ := exp_le_exp.mpr hex

/-- The exact interval [R,N] suffices for the box formulation even at nonintegral N. -/
theorem box_of_uniform_lift {q R : ℕ} {C target N : ℝ}
    (h : UniformLiftBounds (circleLift q) C target q) (hr : 0 < target)
    (hR : exp (C*(q:ℝ)^2) ≤ R) (hR₂ : 2 ≤ R) (hN : (R:ℝ) ≤ N) :
    target ≤ pinnedBoxRatio N := by
  obtain ⟨b,hb,h⟩ := h
  obtain ⟨hl,hu⟩ := h R hR
  have hpos := (mul_pos (mul_pos hr hb) (liftScale_pos hR₂)).trans_le hl
  have hA : (circleLift q R).Nonempty := by
    by_contra! he
    simp [he, rectangleCount] at hpos
  apply (pinnedRatio_ge hA _).trans (pinnedRatio_le_pinnedBoxRatio hA
    (fun k hk i => (circleLift_fitsBox q R k hk i).trans hN))
  calc _ ≤ target * (b * liftScale R) := mul_le_mul_of_nonneg_left hu hr.le
       _ = _ := (mul_assoc ..).symm
       _ ≤ _ := hl

/-- Final reduction to the two uniform fixed-modulus count bounds and the
quantitative product bound on the chosen primes 3 modulo 4. -/
theorem growth_of_lift_bounds {C a D : ℝ} (hC : 1 ≤ C) (ha : 0 < a) (hD : 1 ≤ D)
    (h : ∀ m : ℕ, 2 ≤ m → ∃ q : ℕ, 0 < q ∧ (q:ℝ) ≤ exp (D*m*log m) ∧
      UniformLiftBounds (circleLift q) C (a*(4/3:ℝ)^m) q) : CombinatorialGrowth := by
  let K := 10+2*C+2*D
  apply growth_of_uniform_estimates (K := K) (a := a/32) (by dsimp [K]; linarith) (by positivity)
  · intro m hm N hn
    obtain ⟨q,hq,hp,hl⟩ := h m hm
    obtain ⟨R,hR₂,hR,hw⟩ := exists_lift_window hD hC hq hm hp
    have hRN : (R:ℝ) ≤ N := by
      have h := hw.trans hn
      nlinarith [sq_nonneg (R:ℝ), (Nat.cast_nonneg R : (0:ℝ) ≤ R)]
    refine le_trans ?_ (box_of_uniform_lift hl (by positivity) hR hR₂ hRN)
    gcongr
    linarith
  · intro m hm n hn
    obtain ⟨q,hq,hp,hl⟩ := h m hm
    obtain ⟨R,hR₂,hR,hw⟩ := exists_lift_window hD hC hq hm hp
    have hstart : (2*R+1)^2 ≤ n := by exact_mod_cast hw.trans hn
    have hn₀ : 0 < n := by nlinarith only [hstart, Nat.zero_le R]
    obtain ⟨B,hB,hpB⟩ := exact_size_of_uniform_lift hl (by positivity) (circleLift_mono q)
      (circleLift_card_unbounded hq) rectangleCount_mono maxPinnedCount_mono hR hR₂ hn₀
      ((circleLift_card_le q R).trans hstart)
    calc (a/32)*(4/3:ℝ)^m = (a*(4/3:ℝ)^m)/32 := by ring
         _ ≤ pinnedRatio B := hpB
         _ ≤ pinnedSizeRatio n := hB ▸ pinnedRatio_le_pinnedSizeRatio (card_pos.mp (by omega))

end RTS
