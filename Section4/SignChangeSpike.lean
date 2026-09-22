import Section4.LSeriesPositivity
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LFunction

/-!
# Sign-change feasibility spike

This file records the original analytic feasibility proof that a nonzero level-one cusp form with
real Fourier coefficients has a negative coefficient. It is deliberately not imported by the
production umbrella module `Section4`; the stable public API is in
`Section4.RealCuspSignChange`. The default library build still compiles this file as a regression.
-/

open Filter Set
open scoped ComplexOrder MatrixGroups UpperHalfPlane

namespace Section4.SignChangeSpike

open Section4.LSeriesPositivity

section CuspForm

variable {k : ℤ}

/-- The level-one q-expansion coefficients of a cusp form, isolated to keep the analytic proof
readable. -/
noncomputable def cuspCoeffs (f : CuspForm 𝒮ℒ k) : ℕ → ℂ :=
  fun n ↦ (UpperHalfPlane.qExpansion 1 f).coeff n

lemma cuspCoeffs_zero (f : CuspForm 𝒮ℒ k) : cuspCoeffs f 0 = 0 := by
  exact CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_SL

/-- Q-expansion injectivity supplies a nonzero coefficient of every nonzero cusp form. -/
lemma exists_cuspCoeff_ne_zero {f : CuspForm 𝒮ℒ k} (hf : f ≠ 0) :
    ∃ n, cuspCoeffs f n ≠ 0 := by
  by_contra hcoeff
  push Not at hcoeff
  have hq : UpperHalfPlane.qExpansion 1 (CuspForm.toModularFormₗ f) = 0 := by
    apply PowerSeries.ext
    intro n
    change cuspCoeffs f n = 0
    exact hcoeff n
  have hmf : CuspForm.toModularFormₗ f = 0 :=
    (ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL
      (CuspForm.toModularFormₗ f)).mp hq
  apply hf
  apply CuspForm.toModularFormₗ_injective
  simpa using hmf

/-- The modular L-function agrees with the L-series of the level-one q-expansion in its
half-plane of convergence. -/
lemma L_eq_LSeries_on_right_halfPlane (hk : 0 < k) (f : CuspForm 𝒮ℒ k) :
    {s : ℂ | (k : ℝ) / 2 + 1 < s.re}.EqOn
      (ModularForm.L hk f) (_root_.LSeries (cuspCoeffs f)) := by
  intro s hs
  have hsum : HasSum (fun n ↦ cuspCoeffs f n / (n : ℂ) ^ s)
      (ModularForm.L hk f s) := by
    simpa [cuspCoeffs, Subgroup.strictWidthInfty_SL2Z] using
      CuspForm.hasSum_L hk f hs
  calc
    ModularForm.L hk f s = ∑' n, cuspCoeffs f n / (n : ℂ) ^ s := hsum.tsum_eq.symm
    _ = _root_.LSeries (cuspCoeffs f) s :=
      (LSeries_def₀ (cuspCoeffs_zero f) s).symm

/-- Feasibility target: a nonzero level-one cusp form whose q-expansion is real has a negative
Fourier coefficient. -/
theorem exists_cuspCoeff_re_neg (hk : 0 < k) (f : CuspForm 𝒮ℒ k) (hf : f ≠ 0)
    (hreal : ∀ n, (cuspCoeffs f n).im = 0) :
    ∃ n, (cuspCoeffs f n).re < 0 := by
  by_contra hneg
  push Not at hneg
  have hnonneg : 0 ≤ cuspCoeffs f := fun n ↦ by
    rw [Complex.le_def]
    exact ⟨hneg n, (hreal n).symm⟩
  obtain ⟨n, hn⟩ := exists_cuspCoeff_ne_zero hf
  have hn0 : n ≠ 0 := by
    intro hn_zero
    subst n
    exact hn (cuspCoeffs_zero f)
  have hpos : ∃ n, n ≠ 0 ∧ 0 < cuspCoeffs f n := by
    exact ⟨n, hn0, lt_of_le_of_ne (hnonneg n) (Ne.symm hn)⟩
  let x : ℝ := (k : ℝ) / 2
  have hO : cuspCoeffs f =O[Filter.atTop] fun n ↦ (n : ℝ) ^ x := by
    change (fun n ↦ (UpperHalfPlane.qExpansion 1 f).coeff n) =O[Filter.atTop]
      fun n ↦ (n : ℝ) ^ x
    simpa [x, Subgroup.strictWidthInfty_SL2Z] using
      CuspFormClass.qExpansion_isBigO f
  have habscissa : LSeries.abscissaOfAbsConv (cuspCoeffs f) ≤ ((x + 1 : ℝ) : EReal) := by
    simpa using LSeries.abscissaOfAbsConv_le_of_isBigO_rpow hO
  have hLpos : 0 < ModularForm.L hk f (0 : ℝ) :=
    positive_of_differentiable_of_eqOn_of_exists_pos (x := x + 1) hnonneg hpos
      (CuspForm.differentiable_L hk f) habscissa
      (by simpa [x] using L_eq_LSeries_on_right_halfPlane hk f) 0
  have hLzero : ModularForm.L hk f 0 = 0 := by
    simp [ModularForm.L, Complex.Gammaℂ_def, Complex.Gamma_zero]
  change 0 < ModularForm.L hk f 0 at hLpos
  rw [hLzero] at hLpos
  exact (lt_irrefl (0 : ℂ)) hLpos

/-- Equivalent zero-detection form of the spike, matching the homogeneous half-space intersection
needed by the convex-geometric argument. -/
theorem eq_zero_of_cuspCoeffs_re_nonneg (hk : 0 < k) (f : CuspForm 𝒮ℒ k)
    (hreal : ∀ n, (cuspCoeffs f n).im = 0)
    (hnonneg : ∀ n, 0 ≤ (cuspCoeffs f n).re) :
    f = 0 := by
  by_contra hf
  obtain ⟨n, hn⟩ := exists_cuspCoeff_re_neg hk f hf hreal
  exact (not_lt_of_ge (hnonneg n)) hn

end CuspForm

end Section4.SignChangeSpike
