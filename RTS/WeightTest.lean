module

public import RTS.WeightFamilies
public import RTS.AnalysisDefs
public import RTS.ConfigurationFourier
public import Mathlib.Data.Finsupp.Indicator

/-! # The data and the trigonometric test weight of Section 5 -/

@[expose] public section
noncomputable section
namespace RTS.Dyadic
open Finset MeasureTheory
open scoped BigOperators ENNReal
variable {d : ℕ}

def data (m : Fin d → ℕ) : Freq d →₀ ℂ :=
  Finsupp.indicator ((indexBox m).image (frequency m)) (fun _ _ => 1)

@[simp] theorem data_support (m : Fin d → ℕ) :
    (data m).support = (indexBox m).image (frequency m) := by
  classical
  ext k
  simp [data, Finsupp.mem_support_iff, Finsupp.indicator_apply]

@[simp] theorem data_mem (m : Fin d → ℕ) (k : Freq d) (hk : k ∈ (data m).support) :
    data m k = 1 := by
  rw [data_support] at hk
  unfold data
  exact Finsupp.indicator_of_mem hk _

theorem data_card (m : Fin d → ℕ) : (data m).support.card = ∏ l, m l := by
  rw [data_support, Finset.card_image_of_injective _ (frequency_injective m),indexBox_card]

theorem perWave_data (m : Fin d → ℕ) (x : Torus d) (t : UnitAddCircle) :
    perWave (data m) x t = ∑ j ∈ indexBox m, Configuration.atom (frequency m j)
      (∑ l, (frequency m j l)^2) x t := by
  classical
  unfold perWave
  have H : (∑ k ∈ (data m).support, data m k * UnitAddTorus.mFourier k x * fourier (∑ l, k l^2) t)
      = ∑ k ∈ (data m).support, Configuration.atom k (∑ l, k l^2) x t := by
    exact sum_congr rfl fun k hk => by rw [data_mem m k hk, one_mul]
  rw [H, data_support, sum_image (fun i _ j _ he => frequency_injective m he)]

def auxPoly (m r : Fin d → ℕ) (x : Torus d) (t : UnitAddCircle) : ℂ :=
  ∑ J ∈ family m r, Configuration.atom (spaceFreq m J) (timeFreq m J) x t

def weight (m r : Fin d → ℕ) (z : Torus d × UnitAddCircle) : ℝ :=
  ‖auxPoly m r z.1 z.2‖ ^ 2

@[fun_prop] theorem auxPoly_continuous (m r : Fin d → ℕ) :
    Continuous (fun z : Torus d × UnitAddCircle => auxPoly m r z.1 z.2) := by
  unfold auxPoly Configuration.atom
  fun_prop

theorem weight_valid (m r : Fin d → ℕ) : perWeight (weight m r) := by
  refine ⟨fun _ => sq_nonneg _, ?_⟩
  exact ((auxPoly_continuous m r).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The largest exponent is the sum of the block lengths. -/
theorem data_in_box (m : Fin d → ℕ) {N : ℝ} (hN : (2:ℝ)^(∑ l, m l) ≤ N) :
    perInBox N (data m) := by
  classical
  intro k hk l
  rw [data_support] at hk
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hk
  have hle := (mem_Icc.mp (Fintype.mem_piFinset.mp hq l)).2
  have hs : offset m l + m l ≤ ∑ i, m i := by
    let s := univ.filter (· < l)
    have hnot : l ∉ s := by simp [s]
    have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := m)
      (Finset.subset_univ (insert l s)) (by intros; omega)
    simpa [s,offset,Finset.sum_insert hnot,Nat.add_comm] using hh
  have hp : (2:ℝ)^(offset m l + q l) ≤ 2^(∑ i, m i) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  simpa [frequency, abs_of_nonneg] using hp.trans hN

end RTS.Dyadic
