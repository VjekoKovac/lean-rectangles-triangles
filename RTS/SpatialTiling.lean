module

public import RTS.AnalysisDefs
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Tactic

/-! # Tiling by translates of the period cube

The half-open convention gives an exact partition also on the faces.
-/

@[expose] public section
namespace RTS.Transference
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

def periodCube (d : ℕ) : Set (Space d) :=
  {x | ∀ i, x i ∈ Set.Ioc (0:ℝ) 1}

/-- Periodization of a nonnegative integrand by spatial lattice translates. -/
theorem lintegral_periodize (f : Space d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x) = ∫⁻ x in periodCube d, ∑' j : Freq d, f (x + fun i => (j i : ℝ)) := by
  classical
  let tile (j : Freq d) := Set.univ.pi (fun i => Set.Ioc (j i : ℝ) (j i + 1))
  have ht (j : Freq d) : MeasurableSet (tile j) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ioc)
  have hkey (j : Freq d) (x : Space d) : x ∈ tile j ↔ ∀ i, ⌈x i⌉ = j i + 1 := by
    simp only [tile, Set.mem_univ_pi, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
      add_sub_cancel_right, Set.mem_Ioc]
  have hcover : (⋃ j : Freq d, tile j) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨fun i => ⌈x i⌉ - 1, ?_⟩
    exact (hkey _ _).mpr fun i => by simp
  have hdis : Pairwise (fun j k => Disjoint (tile j) (tile k)) := by
    intro j k hjk
    refine Set.disjoint_left.mpr fun x hx hy => hjk (funext fun i => ?_)
    have h1 := (hkey j x).mp hx i
    have h2 := (hkey k x).mp hy i
    omega
  have htrans (j : Freq d) :
      (∫⁻ x in tile j, f x) = ∫⁻ x in periodCube d, f (x + fun i => (j i : ℝ)) := by
    let a : Space d := fun i => (j i : ℝ)
    have he : (fun x : Space d => x + a) ⁻¹' tile j = periodCube d := by
      ext x
      simp only [tile, periodCube, Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq, Set.mem_Ioc,
        Pi.add_apply, a]
      exact forall_congr' fun i => by constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    have hh := (measurePreserving_add_right (volume : Measure (Space d)) a).setLIntegral_comp_preimage
      (ht j) hf
    rw [he] at hh
    exact hh.symm
  calc
    (∫⁻ x, f x) = ∫⁻ x in ⋃ j, tile j, f x := by simp [hcover]
    _ = ∑' j, ∫⁻ x in tile j, f x := lintegral_iUnion ht hdis f
    _ = ∑' j : Freq d, ∫⁻ x in periodCube d, f (x + fun i => (j i : ℝ)) :=
      tsum_congr htrans
    _ = _ := (lintegral_tsum (fun j : Freq d => (hf.comp
      (measurable_id.add measurable_const)).aemeasurable)).symm

end RTS.Transference
