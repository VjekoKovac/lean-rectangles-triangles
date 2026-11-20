module

public import RTS.CombinatorialTheorem
public import RTS.TransferenceProof
public import RTS.ConfigurationProof
public import RTS.Weights

/-! Proved introductory theorems. Each declaration below is checked independently
against its counterpart in Challenge.lean. -/

@[expose] public section
namespace RTS

/-- Theorem 1.2 of arXiv:2606.30178v1. -/
theorem combinatorial_growth : CombinatorialGrowth :=
  combinatorialGrowth

/-- Theorem 1.3 of arXiv:2606.30178v1. -/
theorem quantitative_transference : QuantitativeTransference :=
  quantitativeTransference

/-- Theorem 1.4 of arXiv:2606.30178v1. -/
theorem configuration_lower_bounds : ConfigurationLowerBounds :=
  Configuration.configurationLowerBounds

/-- Theorem 1.5 of arXiv:2606.30178v1. -/
theorem trigonometric_growth : TrigonometricGrowth :=
  Dyadic.trigonometricGrowth

end RTS
