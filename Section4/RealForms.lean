import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Real q-expansions and real level-one modular forms

This file defines the real forms used by the Section 4 formalization.  The reality condition is
coefficientwise and is first packaged for an arbitrary group and admissible q-expansion width.
The level-one spaces and their coefficient maps are then obtained by specializing to width one.

Coordinates are deliberately separated into the `Coordinates` namespace.  Public definitions
of real and normalized modular forms do not depend on a basis.
-/

open scoped MatrixGroups UpperHalfPlane

namespace Section4.RealForms

open UpperHalfPlane

/-- A bundled function has a real q-expansion at width `h` if every coefficient has zero
imaginary part. -/
def HasRealQExpansionAt {F : Type*} [FunLike F ℍ ℂ] (h : ℝ) (f : F) : Prop :=
  ∀ n : ℕ, ((qExpansion h f).coeff n).im = 0

/-- The real part of the `n`th q-expansion coefficient at width `h`. -/
noncomputable def realQCoeffAt {F : Type*} [FunLike F ℍ ℂ]
    (h : ℝ) (f : F) (n : ℕ) : ℝ :=
  ((qExpansion h f).coeff n).re

variable (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) (h : ℝ)

/-- Modular forms for `Γ` whose q-expansion at `h` is coefficientwise real. -/
def realModularFormSubmodule (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Submodule ℝ (ModularForm Γ k) where
  carrier := {f | HasRealQExpansionAt h f}
  zero_mem' n := by
    change ((qExpansion h (0 : ℍ → ℂ)).coeff n).im = 0
    rw [qExpansion_zero]
    simp
  add_mem' {f g} hf hg n := by
    change ((qExpansion h (⇑f + ⇑g)).coeff n).im = 0
    rw [ModularForm.qExpansion_add hh hΓ]
    simp [hf n, hg n]
  smul_mem' r f hf n := by
    change ((qExpansion h ((r : ℂ) • (f : ℍ → ℂ))).coeff n).im = 0
    rw [ModularForm.qExpansion_smul hh hΓ]
    simp [hf n]

/-- Cusp forms for `Γ` whose q-expansion at `h` is coefficientwise real. -/
def realCuspFormSubmodule (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Submodule ℝ (CuspForm Γ k) where
  carrier := {f | HasRealQExpansionAt h f}
  zero_mem' n := by
    change ((qExpansion h (0 : ℍ → ℂ)).coeff n).im = 0
    rw [qExpansion_zero]
    simp
  add_mem' {f g} hf hg n := by
    change ((qExpansion h (⇑f + ⇑g)).coeff n).im = 0
    rw [ModularForm.qExpansion_add hh hΓ]
    simp [hf n, hg n]
  smul_mem' r f hf n := by
    change ((qExpansion h ((r : ℂ) • (f : ℍ → ℂ))).coeff n).im = 0
    rw [ModularForm.qExpansion_smul hh hΓ]
    simp [hf n]

@[simp] theorem mem_realModularFormSubmodule (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (f : ModularForm Γ k) :
    f ∈ realModularFormSubmodule Γ k h hh hΓ ↔ HasRealQExpansionAt h f :=
  Iff.rfl

@[simp] theorem mem_realCuspFormSubmodule (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (f : CuspForm Γ k) :
    f ∈ realCuspFormSubmodule Γ k h hh hΓ ↔ HasRealQExpansionAt h f :=
  Iff.rfl

/-- Level-one modular forms with coefficientwise-real q-expansion. -/
abbrev RealModularForm (k : ℤ) :=
  realModularFormSubmodule 𝒮ℒ k 1 one_pos one_mem_strictPeriods_SL

/-- Level-one cusp forms with coefficientwise-real q-expansion. -/
abbrev RealCuspForm (k : ℤ) :=
  realCuspFormSubmodule 𝒮ℒ k 1 one_pos one_mem_strictPeriods_SL

namespace RealModularForm

variable {k : ℤ}

/-- The real `n`th q-expansion coefficient of a real level-one modular form. -/
noncomputable def coeff (f : RealModularForm k) (n : ℕ) : ℝ :=
  realQCoeffAt 1 (f : ModularForm 𝒮ℒ k) n

/-- Evaluation of a fixed q-expansion coefficient is real-linear on real modular forms. -/
noncomputable def coeffLinear (n : ℕ) : RealModularForm k →ₗ[ℝ] ℝ where
  toFun f := coeff f n
  map_add' f g := by
    change ((qExpansion 1 (⇑(f : ModularForm 𝒮ℒ k) + ⇑(g : ModularForm 𝒮ℒ k))).coeff n).re = _
    rw [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL]
    simp [coeff, realQCoeffAt]
  map_smul' r f := by
    change ((qExpansion 1 ((r : ℂ) • ⇑(f : ModularForm 𝒮ℒ k))).coeff n).re = _
    rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
    simp [coeff, realQCoeffAt]

@[simp] theorem coeffLinear_apply (n : ℕ) (f : RealModularForm k) :
    coeffLinear n f = coeff f n :=
  rfl

theorem hasRealQExpansionAt (f : RealModularForm k) :
    HasRealQExpansionAt 1 (f : ModularForm 𝒮ℒ k) :=
  f.property

/-- Real q-expansion coefficients determine a real level-one modular form. -/
theorem ext {f g : RealModularForm k} (hfg : ∀ n, coeff f n = coeff g n) : f = g := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL]
  change qExpansion 1 (⇑(f : ModularForm 𝒮ℒ k) - ⇑(g : ModularForm 𝒮ℒ k)) = 0
  rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
  apply sub_eq_zero.mpr
  ext n
  apply Complex.ext
  · simpa [coeff, realQCoeffAt] using hfg n
  · rw [f.property n, g.property n]

/-- The complete real coefficient sequence is injective. -/
theorem coeff_injective : Function.Injective (fun f : RealModularForm k ↦ coeff f) := by
  intro f g h
  exact ext fun n ↦ congrFun h n

/-- The real level-one modular-form space is finite-dimensional over `ℝ`. -/
noncomputable instance finiteDimensional : FiniteDimensional ℝ (RealModularForm k) := by
  let _ : FiniteDimensional ℝ (ModularForm 𝒮ℒ k) :=
    FiniteDimensional.trans ℝ ℂ (ModularForm 𝒮ℒ k)
  infer_instance

end RealModularForm

namespace RealCuspForm

variable {k : ℤ}

/-- The real `n`th q-expansion coefficient of a real level-one cusp form. -/
noncomputable def coeff (f : RealCuspForm k) (n : ℕ) : ℝ :=
  realQCoeffAt 1 (f : CuspForm 𝒮ℒ k) n

/-- Evaluation of a fixed q-expansion coefficient is real-linear on real cusp forms. -/
noncomputable def coeffLinear (n : ℕ) : RealCuspForm k →ₗ[ℝ] ℝ where
  toFun f := coeff f n
  map_add' f g := by
    change ((qExpansion 1 (⇑(f : CuspForm 𝒮ℒ k) + ⇑(g : CuspForm 𝒮ℒ k))).coeff n).re = _
    rw [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL]
    simp [coeff, realQCoeffAt]
  map_smul' r f := by
    change ((qExpansion 1 ((r : ℂ) • ⇑(f : CuspForm 𝒮ℒ k))).coeff n).re = _
    rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
    simp [coeff, realQCoeffAt]

@[simp] theorem coeffLinear_apply (n : ℕ) (f : RealCuspForm k) :
    coeffLinear n f = coeff f n :=
  rfl

theorem hasRealQExpansionAt (f : RealCuspForm k) :
    HasRealQExpansionAt 1 (f : CuspForm 𝒮ℒ k) :=
  f.property

/-- Inclusion of real cusp forms into real modular forms. -/
noncomputable def toRealModularForm : RealCuspForm k →ₗ[ℝ] RealModularForm k where
  toFun f := ⟨CuspForm.toModularFormₗ (f : CuspForm 𝒮ℒ k), f.property⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add CuspForm.toModularFormₗ (f : CuspForm 𝒮ℒ k) g
  map_smul' r f := by
    apply Subtype.ext
    simp

@[simp] theorem coe_toRealModularForm (f : RealCuspForm k) :
    (toRealModularForm f : ModularForm 𝒮ℒ k) =
      CuspForm.toModularFormₗ (f : CuspForm 𝒮ℒ k) :=
  rfl

@[simp] theorem coeff_toRealModularForm (f : RealCuspForm k) (n : ℕ) :
    RealModularForm.coeff (toRealModularForm f) n = coeff f n :=
  rfl

theorem toRealModularForm_injective : Function.Injective (toRealModularForm (k := k)) := by
  intro f g hfg
  apply Subtype.ext
  apply CuspForm.toModularFormₗ_injective
  exact congrArg Subtype.val hfg

/-- Real q-expansion coefficients determine a real level-one cusp form. -/
theorem ext {f g : RealCuspForm k} (hfg : ∀ n, coeff f n = coeff g n) : f = g := by
  apply toRealModularForm_injective
  apply RealModularForm.ext
  intro n
  simpa using hfg n

/-- The complete real coefficient sequence is injective on real cusp forms. -/
theorem coeff_injective : Function.Injective (fun f : RealCuspForm k ↦ coeff f) := by
  intro f g h
  exact ext fun n ↦ congrFun h n

@[simp] theorem coeff_zero (f : RealCuspForm k) : coeff f 0 = 0 := by
  simp [coeff, realQCoeffAt, CuspFormClass.qExpansion_coeff_zero]

/-- The real level-one cusp-form space is finite-dimensional over `ℝ`. -/
noncomputable instance finiteDimensional : FiniteDimensional ℝ (RealCuspForm k) := by
  let _ : FiniteDimensional ℂ (CuspForm 𝒮ℒ k) :=
    FiniteDimensional.of_injective CuspForm.toModularFormₗ
      CuspForm.toModularFormₗ_injective
  let _ : FiniteDimensional ℝ (CuspForm 𝒮ℒ k) :=
    FiniteDimensional.trans ℝ ℂ (CuspForm 𝒮ℒ k)
  infer_instance

namespace Coordinates

noncomputable section

/-- The dimension of the real level-one cusp-form space. -/
abbrev dimension (k : ℤ) : ℕ := Module.finrank ℝ (RealCuspForm k)

/-- A Euclidean coordinate space of the correct dimension for real cusp forms. -/
abbrev Space (k : ℤ) := Fin (dimension k) → ℝ

/-- A noncomputably chosen coordinate equivalence from Euclidean space to real cusp forms.
No choice of basis enters the definitions of `RealCuspForm` or `RealModularForm`. -/
noncomputable def toForm (k : ℤ) : Space k ≃ₗ[ℝ] RealCuspForm k :=
  (Module.finBasis ℝ (RealCuspForm k)).equivFun.symm

/-- The coordinate vector of a real cusp form. -/
noncomputable def ofForm (k : ℤ) : RealCuspForm k ≃ₗ[ℝ] Space k :=
  (toForm k).symm

@[simp] theorem toForm_ofForm (f : RealCuspForm k) :
    toForm k (ofForm k f) = f :=
  (toForm k).apply_symm_apply f

@[simp] theorem ofForm_toForm (v : Space k) :
    ofForm k (toForm k v) = v :=
  (toForm k).symm_apply_apply v

/-- The `n`th cusp coefficient pulled back to Euclidean coordinates as a linear map. -/
noncomputable def coeffLinear (n : ℕ) : Space k →ₗ[ℝ] ℝ :=
  (RealCuspForm.coeffLinear n).comp (toForm k).toLinearMap

@[simp] theorem coeffLinear_apply (n : ℕ) (v : Space k) :
    coeffLinear n v = RealCuspForm.coeff (toForm k v) n :=
  rfl

/-- The `n`th coordinate coefficient functional, bundled as a continuous real-linear map. -/
noncomputable def coeffContinuous (n : ℕ) : Space k →L[ℝ] ℝ :=
  (coeffLinear n).toContinuousLinearMap

@[simp] theorem coeffContinuous_apply (n : ℕ) (v : Space k) :
    coeffContinuous n v = RealCuspForm.coeff (toForm k v) n :=
  rfl

end

end Coordinates

end RealCuspForm

/-- A normalized real level-one modular form has constant coefficient one. -/
def NormalizedRealModularForm (k : ℤ) :=
  {f : RealModularForm k // RealModularForm.coeff f 0 = 1}

namespace NormalizedRealModularForm

variable {k : ℤ}

/-- The real `n`th coefficient of a normalized real modular form. -/
noncomputable def coeff (f : NormalizedRealModularForm k) (n : ℕ) : ℝ :=
  RealModularForm.coeff f.1 n

@[simp] theorem coeff_zero (f : NormalizedRealModularForm k) : coeff f 0 = 1 :=
  f.property

end NormalizedRealModularForm

end Section4.RealForms
