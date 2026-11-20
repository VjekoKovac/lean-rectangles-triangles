module

public import RTS.CRTMembership
public import RTS.CircleLift
public import RTS.LatticeGeometry
public import RTS.LiftingAbel
public import RTS.LiftingResidues

/-! The modular and size constraints on primitive parameters in §2.3. -/
@[expose] public noncomputable section
namespace RTS.Lifting

open Finset
variable (P : CRT.PrimeSet)

theorem circleLift_radius {N : ℕ} {w : Point} :
    w ∈ circleLift P.modulus N ↔ (radius w : ℝ) ≤ N ∧ reduce P.modulus w ∈ P.circle := by
  rw [mem_circleLift, radius_le_iff,P.circle_iff, ← ZMod.intCast_eq_intCast_iff]
  apply and_congr
  · apply forall_congr'
    intro i
    rw [abs_le]
    exact_mod_cast Iff.rfl
  · simp [dot₂, Fin.sum_univ_two, reduce, sq]

@[simp] theorem reduce_add (q : ℕ) (x y : Point) : reduce q (x+y) = reduce q x + reduce q y := by
  funext i; simp [reduce]
@[simp] theorem reduce_sub (q : ℕ) (x y : Point) : reduce q (x-y) = reduce q x - reduce q y := by
  funext i; simp [reduce]
@[simp] theorem reduce_smul (q : ℕ) (r : ℤ) (w : Point) :
    reduce q (r • w) = (r : ZMod q) • reduce q w := by
  funext i; change ((r * w i : ℤ) : ZMod q) = (r : ZMod q) * (w i : ZMod q); push_cast; rfl
@[simp] theorem reduce_rot (w : Point) : reduce P.modulus (rot w) = P.turn (reduce P.modulus w) := by
  funext i; fin_cases i <;> simp [reduce, rot, CRT.PrimeSet.turn]

theorem radius_add_le (u v : Point) : (radius (u+v) : ℝ) ≤ radius u + radius v := by
  apply (radius_le_iff ..).2
  intro i
  simp only [Pi.add_apply, Int.cast_add]
  exact (abs_add_le ..).trans (add_le_add ((radius_le_iff u _).mp le_rfl i)
    ((radius_le_iff v _).mp le_rfl i))

@[simp] theorem radius_neg (w : Point) : radius (-w) = radius w := by simp [radius]
@[simp] theorem radius_rot (w : Point) : radius (rot w) = radius w := by simp [radius,rot,max_comm]
theorem radius_smul (r : ℤ) (w : Point) : radius (r • w) = r.natAbs * radius w := by
  change max ((r*w 0).natAbs) ((r*w 1).natAbs) = _
  simp only [radius, Int.natAbs_mul, Nat.mul_max_mul_left]

theorem radius_smul_real (r : ℤ) (w : Point) : (radius (r • w) : ℝ) = |(r:ℝ)| * radius w := by
  rw [radius_smul, Nat.cast_mul]
  congr 1
  rw [Nat.cast_natAbs,Int.cast_abs]

theorem radius_sub_le (u v : Point) : (radius (u-v) : ℝ) ≤ radius u + radius v := by
  simpa [sub_eq_add_neg] using radius_add_le u (-v)

/-- All four corners of a rectangle in the sampled quarter-box lie in the lifted circle. -/
theorem sample_corners_mem {N : ℕ} {x w : Point} {r s : ℤ}
    (hres : (reduce P.modulus x,reduce P.modulus w,(r:P.R),(s:P.R)) ∈ P.rects)
    (hx : (radius x : ℝ) ≤ N/4) (hr : |(r:ℝ)| * radius w ≤ N/4)
    (hs : |(s:ℝ)| * radius w ≤ N/4) :
    let y := corners (x,w,r,s)
    y.1 ∈ circleLift P.modulus N ∧ y.2.1 ∈ circleLift P.modulus N ∧
    y.2.2.1 ∈ circleLift P.modulus N ∧ y.2.2.2 ∈ circleLift P.modulus N := by
  obtain ⟨_,h₀,h₁,h₂,h₃⟩ := (P.rects_iff ..).mp hres
  dsimp only [corners,sides]
  simp only [circleLift_radius P,reduce_add,reduce_smul,reduce_rot]
  have hru := radius_add_le x (r • w)
  have hsv := radius_add_le x (s • rot w)
  have hcc := radius_add_le (x+r • w) (s • rot w)
  simp only [radius_smul_real,radius_rot] at hru hsv hcc
  exact ⟨⟨by linarith,h₀⟩,⟨by linarith,h₁⟩,⟨by linarith,h₃⟩,⟨by linarith,h₂⟩⟩

/-- The two integer endpoints give the two modular base points in the pinned test. -/
theorem pin_residue {N : ℕ} {a b k w : Point} {r s : ℤ}
    (ha : a ∈ circleLift P.modulus N) (hb : b ∈ circleLift P.modulus N)
    (hw : Primitive w) (he : sides (w,r,s) = triangleSides k (a,b)) :
    (reduce P.modulus w,(r:P.R),(s:P.R)) ∈ P.pins (reduce P.modulus k) := by
  have hu : r • w = b-a := congrArg Prod.fst he
  have hv : s • rot w = (2:ℤ) • k-a-b := congrArg Prod.snd he
  have h₁ := congrArg (reduce P.modulus) hu
  have h₂ := congrArg (reduce P.modulus) hv
  simp only [reduce_smul,reduce_sub,reduce_rot,Int.cast_ofNat] at h₁ h₂
  rw [P.pins_iff,h₁,h₂]
  refine ⟨P.primitive_goodDirection hw, ?_, ?_⟩
  · convert (circleLift_radius P).mp ha |>.2 using 1
    have hn := P.two_mul_half
    ext i
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    linear_combination (reduce P.modulus a i - reduce P.modulus k i) * hn
  · convert (circleLift_radius P).mp hb |>.2 using 1
    have hn := P.two_mul_half
    ext i
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    linear_combination (reduce P.modulus b i - reduce P.modulus k i) * hn

/-- The pinned sampling bounds cover both zero-side degeneracies. -/
theorem pin_sizes {N : ℕ} {a b k w : Point} {r s : ℤ}
    (ha : a ∈ circleLift P.modulus N) (hb : b ∈ circleLift P.modulus N)
    (hk : k ∈ circleLift P.modulus N) (hne : r ≠ 0 ∨ s ≠ 0)
    (he : sides (w,r,s) = triangleSides k (a,b)) :
    (radius w : ℝ) ≤ 4*N ∧ |(r:ℝ)| * radius w ≤ 4*N ∧ |(s:ℝ)| * radius w ≤ 4*N := by
  have hA := ((circleLift_radius P).mp ha).1
  have hB := ((circleLift_radius P).mp hb).1
  have hK := ((circleLift_radius P).mp hk).1
  have hu : r • w = b-a := congrArg Prod.fst he
  have hv : s • rot w = (2:ℤ) • k-a-b := congrArg Prod.snd he
  have h₁ := radius_sub_le b a
  rw [← hu,radius_smul_real] at h₁
  have h₂ := radius_sub_le ((2:ℤ) • k-a) b
  have h₃ := radius_sub_le ((2:ℤ) • k) a
  rw [← hv,radius_smul_real,radius_rot] at h₂
  have hsm : (radius ((2:ℤ) • k) : ℝ) = 2 * radius k :=
    (radius_smul_real 2 k).trans (by norm_num)
  rw [hsm] at h₃
  refine ⟨?_,by linarith,by linarith⟩
  have mul_one_le (t : ℤ) (ht : t ≠ 0) : (radius w : ℝ) ≤ |(t:ℝ)| * radius w := by
    apply le_mul_of_one_le_left (by positivity)
    exact_mod_cast Int.one_le_abs ht
  rcases hne with h|h
  · linarith [mul_one_le _ h]
  · linarith [mul_one_le _ h]

end RTS.Lifting
