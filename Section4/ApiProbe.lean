import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.LSeries.Positivity

/-!
# API probes for the Section 4 formalization

This diagnostic module records the compiled mathlib API checks used in Task 1. It contains no
theorem from the paper and is deliberately not imported by the production umbrella module
`Section4`. The default library build still compiles it as an audit regression.
-/

open scoped MatrixGroups UpperHalfPlane

#check UpperHalfPlane.qExpansion
#check ModularForm.qExpansion_eq_zero_iff
#check ModularForm.qExpansionAddHom
#check ModularForm.qExpansionRingHom
#check CuspFormClass.qExpansion_coeff_zero

#check EisensteinSeries.q_expansion_bernoulli
#check EisensteinSeries.E_qExpansion_coeff
#check EisensteinSeries.E_qExpansion_coeff_zero
#check EisensteinSeries.E_ne_zero

#check ModularForm.dimension_level_one
#check ModularForm.sturm_bound_levelOne_nat
#check ModularForm.rank_eq_one_add_rank_cuspForm
#check CuspForm.rank_eq_zero_of_weight_lt_twelve
#check ModularForm.CuspForm.equivCuspFormSubmodule
#check ModularForm.toCuspForm
#check ModularForm.isCuspForm_iff_coeffZero_eq_zero

#check CuspFormClass.qExpansion_isBigO
#check ModularFormClass.qExpansion_isBigO

#check ModularForm.weakFEPair
#check ModularForm.Λ
#check ModularForm.L
#check CuspForm.isStrongFEPair
#check CuspForm.differentiable_Λ
#check CuspForm.differentiable_L
#check CuspForm.hasSum_L
#check Subgroup.strictWidthInfty_SL2Z
#check LSeries.positive
#check LSeries.positive_of_differentiable_of_eqOn
#check LSeries.abscissaOfAbsConv_le_of_isBigO_rpow

#check isCompact_sphere
#check IsCompact.elim_finite_subcover

noncomputable example : FiniteDimensional ℂ (ModularForm 𝒮ℒ (12 : ℤ)) := inferInstance

noncomputable example : Module ℝ (CuspForm 𝒮ℒ (12 : ℤ)) := inferInstance

namespace Section4.ApiProbe

/-- The fixed-weight coefficient map is complex-linear, although mathlib currently bundles only
the additive q-expansion map. -/
noncomputable def modularQCoeff (k : ℤ) (n : ℕ) : ModularForm 𝒮ℒ k →ₗ[ℂ] ℂ where
  toFun f := (UpperHalfPlane.qExpansion 1 f).coeff n
  map_add' f g := by
    change (UpperHalfPlane.qExpansion 1 (⇑f + ⇑g)).coeff n = _
    rw [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL]
    simp
  map_smul' c f := by
    change (UpperHalfPlane.qExpansion 1 (c • ⇑f)).coeff n = _
    rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
    simp

/-- The same fixed-weight coefficient map on cusp forms. -/
noncomputable def cuspQCoeff (k : ℤ) (n : ℕ) : CuspForm 𝒮ℒ k →ₗ[ℂ] ℂ where
  toFun f := (UpperHalfPlane.qExpansion 1 f).coeff n
  map_add' f g := by
    change (UpperHalfPlane.qExpansion 1 (⇑f + ⇑g)).coeff n = _
    rw [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL]
    simp
  map_smul' c f := by
    change (UpperHalfPlane.qExpansion 1 (c • ⇑f)).coeff n = _
    rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
    simp

/-- Finite-dimensionality of cusp forms is derivable from the supplied injection into modular
forms, but is not currently registered as a typeclass instance. -/
noncomputable example : FiniteDimensional ℂ (CuspForm 𝒮ℒ (12 : ℤ)) :=
  FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

/-- Restriction of scalars supplies a finite-dimensional real model once the missing complex
instance is installed locally. -/
noncomputable example : FiniteDimensional ℝ (CuspForm 𝒮ℒ (12 : ℤ)) := by
  let _ : FiniteDimensional ℂ (CuspForm 𝒮ℒ (12 : ℤ)) :=
    FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
  exact FiniteDimensional.trans ℝ ℂ (CuspForm 𝒮ℒ (12 : ℤ))

/-- The ordinary modular-form L-function vanishes at zero directly from its definition and the
zero of the reciprocal archimedean Gamma factor. -/
example {k : ℤ} (hk : 0 < k) (f : ModularForm 𝒮ℒ k) : ModularForm.L hk f 0 = 0 := by
  simp [ModularForm.L, Complex.Gammaℂ_def, Complex.Gamma_zero]

end Section4.ApiProbe
