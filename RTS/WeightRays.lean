module

public import RTS.WeightTest
public import RTS.ConfigurationCounts
public import RTS.RayCharacters

/-! Every ray of velocity `2k` tested by the dyadic construction sees exactly the
diagonal terms. This gives the normalized X-ray mass for each basepoint. -/
@[expose] public section

noncomputable section
namespace RTS.Dyadic

open MeasureTheory Configuration
open scoped ENNReal BigOperators ComplexConjugate
variable {d : ℕ}

/-- Evaluation of the X-ray integral uses finite Fourier orthogonality and injectivity
of the time frequencies obtained on the ray. -/
theorem dyadicXray (m q r : Fin d → ℕ) (x : Torus d) :
    perXray (weight m r) x (frequency m q) = (family m r).card := by
  classical
  let v (J : Fin d → Finset ℕ) := UnitAddTorus.mFourier (spaceFreq m J) x
  let g (t : UnitAddCircle) := ‖auxPoly m r (fun i => x i - (2 * frequency m q i) • t) t‖ ^ 2
  have hline : Continuous (fun t : UnitAddCircle => (fun i => x i - (2 * frequency m q i) • t : Torus d)) :=
    continuous_pi fun i => continuous_const.sub (continuous_zsmul _)
  have hc : Continuous g := (((auxPoly_continuous m r).comp
    (hline.prodMk continuous_id)).norm).pow 2
  have hnonneg : 0 ≤ᵐ[circleMeasure] g := Filter.Eventually.of_forall fun _ => sq_nonneg _
  have haux (t : UnitAddCircle) :
      auxPoly m r (fun i => x i - (2 * frequency m q i) • t) t =
        ∑ J ∈ family m r, v J * fourier (lineFreq m q J) t := by
    unfold auxPoly
    exact Finset.sum_congr rfl fun J _ => atom_on_ray _ _ _ _ _
  have hdiag : (((family m r) ×ˢ (family m r)).filter
      (fun p => lineFreq m q p.1 = lineFreq m q p.2)) = (family m r).diag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
    exact ⟨fun ⟨⟨h₁,h₂⟩, he⟩ => ⟨h₁, lineFreq_injOn m q r h₁ h₂ he⟩,
      fun ⟨h₁, he⟩ => ⟨⟨h₁, he ▸ h₁⟩, congrArg _ he⟩⟩
  have hv (J : Fin d → Finset ℕ) : ‖v J‖ = 1 := by
    simp only [v, UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
      Circle.norm_coe, Finset.prod_const_one]
  have he := circle_energy (family m r) v (lineFreq m q)
  rw [hdiag, Finset.sum_diag] at he
  simp only [Complex.mul_conj', hv, one_pow, Complex.ofReal_one, Finset.sum_const,
    nsmul_eq_mul, mul_one, ← haux, integral_complex_ofReal] at he
  have hr := congrArg Complex.re he
  simp only [Complex.ofReal_re, Complex.natCast_re] at hr
  change (∫ t, g t ∂circleMeasure) = ((family m r).card : ℝ) at hr
  change (∫⁻ t, ENNReal.ofReal (g t) ∂circleMeasure) = _
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) hnonneg, hr, ENNReal.ofReal_natCast]

theorem dyadicMTDenom_le (m r : Fin d → ℕ) :
    perRHS .mt (data m) (weight m r) ≤ ((indexBox m).card : ℝ≥0∞) * (family m r).card := by
  classical
  have hs : (∑ k ∈ (data m).support, ‖data m k‖ₑ ^ 2) = ((indexBox m).card : ℝ≥0∞) := by
    calc
      _ = ∑ _k ∈ (data m).support, (1 : ℝ≥0∞) := Finset.sum_congr rfl
        (fun k hk => by simp [data_mem m k hk])
      _ = _ := by simp [Finset.card_image_of_injective _ (frequency_injective m)]
  simp only [perRHS, hs]
  apply mul_le_mul_right
  refine iSup_le fun k => iSup_le fun x => ?_
  have hk : (k : Freq d) ∈ (indexBox m).image (frequency m) := by
    rw [← data_support]
    exact k.property
  obtain ⟨q,_,hq⟩ := Finset.mem_image.mp hk
  rw [← hq, dyadicXray]

end RTS.Dyadic
