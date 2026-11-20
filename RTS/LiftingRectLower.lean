module

public import RTS.LiftingTupleCards
public import RTS.LiftingPrimitiveBounds
public import RTS.LiftingThreshold

/-! A lower bound for each residue class of rectangle parameters, with all constants
uniform in the modulus. The quarter-box is the one used in the paper. Restricting
the primitive direction to radius N/(8q) keeps the side intervals long enough
to use their lower bounds separately. -/
@[expose] public noncomputable section

namespace RTS.Lifting
open Finset Real

theorem rectFiber_lower {q : ℕ} (hq : 0 < q) (e : RectResidue q)
    (ha : ((e.2.1 0).val.gcd (e.2.1 1).val).Coprime q)
    {N : ℝ} (hN : exp (1000*(q:ℝ)^2) ≤ N) :
    N^4 * log N / (1024*(q:ℝ)^6) ≤ (rectFiber q e N).card := by
  let T := N / (8*(q:ℝ))
  let U := N / 4
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hn : 0 < N := (exp_pos _).trans_le hN
  obtain ⟨hT,hU,_,hlog⟩ := lifting_threshold hq hN
  have hX : (U / q)^2 ≤ (pointsInResidue q e.1 U).card :=
    x_square_lower hq e.1 (by dsimp [U]; convert hU using 1; ring)
  have hdir : log N / (2*(q:ℝ)^2) ≤ ∑ w ∈ directions q e.2.1 T, 1 / (radius w:ℝ)^2 :=
    hlog.trans (directions_lower hq e.2.1 ha hT)
  have picks_bound (w : Point) (hw : w ∈ directions q e.2.1 T) :
      (U / q)^2 / 2 * (1 / (radius w : ℝ)^2) ≤ (picks q e.2.2.1 e.2.2.2 (U/radius w)).card := by
    obtain ⟨hp, hrad, _⟩ := (mem_directions hq).mp hw
    have hpos : (0:ℝ) < radius w := by exact_mod_cast radius_pos (primitive_ne_zero hp)
    have hLen : 2 ≤ U / (radius w : ℝ) / q := by
      apply (le_div_iff₀ hq').mpr
      apply (le_div_iff₀ hpos).mpr
      have hmul := (le_div_iff₀ (by positivity : 0 < 8*(q:ℝ))).mp hrad
      dsimp [U]
      linarith only [hmul]
    apply le_trans _ (picks_lower hq e.2.2.1 e.2.2.2 hLen)
    ring_nf
    rfl
  have hS : (U/q)^2 / 2 * (log N / (2*(q:ℝ)^2)) ≤ (sideFiber q e.2 T U).card := by
    calc
      _ ≤ (U/q)^2 / 2 * ∑ w ∈ directions q e.2.1 T, 1/(radius w:ℝ)^2 :=
        mul_le_mul_of_nonneg_left hdir (by positivity)
      _ ≤ _ := by
        rw [sideFiber_card, Nat.cast_sum, Finset.mul_sum]
        exact Finset.sum_le_sum picks_bound
  change _ ≤ ((pointsInResidue q e.1 U ×ˢ sideFiber q e.2 T U).card:ℝ)
  rw [card_product, Nat.cast_mul]
  calc
    _ = (U/q)^2 * ((U/q)^2/2 * (log N/(2*(q:ℝ)^2))) := by dsimp [U]; ring
    _ ≤ _ := mul_le_mul hX hS
      (by have : 0 ≤ log N := log_nonneg (by linarith : 1 ≤ N); positivity) (by positivity)

theorem rectTupleSet_lower {q : ℕ} (hq : 0 < q) (E : Finset (RectResidue q))
    (hE : ∀ e ∈ E, ((e.2.1 0).val.gcd (e.2.1 1).val).Coprime q)
    {N : ℝ} (hN : exp (1000*(q:ℝ)^2) ≤ N) :
    E.card * (N^4 * log N / (1024*(q:ℝ)^6)) ≤ (rectTupleSet q E N).card := by
  rw [rectTupleSet_card hq, Nat.cast_sum]
  calc _ = ∑ _ ∈ E, N^4 * log N / (1024*(q:ℝ)^6) := by simp
       _ ≤ _ := Finset.sum_le_sum fun e he => rectFiber_lower hq e (hE e he) hN

end RTS.Lifting
