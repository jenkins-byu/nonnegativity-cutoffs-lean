import Section4.LSeriesPositivity
import Section4.RealForms
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.LFunction

/-!
# Sign change for real level-one cusp forms

This file promotes the Task 2 feasibility spike to the invariant real-form API.  Its public
theorems contain no raw conditions on imaginary parts of complex coefficients.
-/

open Filter Set
open scoped ComplexOrder MatrixGroups UpperHalfPlane

namespace Section4.RealForms.RealCuspForm

variable {k : ℤ}

/-- The underlying complex q-expansion coefficients.  This is private to the analytic proof;
the public API uses `RealCuspForm.coeff`. -/
private noncomputable def complexCoeffs (f : RealCuspForm k) : ℕ → ℂ :=
  fun n ↦ (UpperHalfPlane.qExpansion 1 (f : CuspForm 𝒮ℒ k)).coeff n

private lemma complexCoeffs_zero (f : RealCuspForm k) : complexCoeffs f 0 = 0 := by
  exact CuspFormClass.qExpansion_coeff_zero (f : CuspForm 𝒮ℒ k) one_pos
    one_mem_strictPeriods_SL

private lemma exists_complexCoeff_ne_zero {f : RealCuspForm k} (hf : f ≠ 0) :
    ∃ n, complexCoeffs f n ≠ 0 := by
  have hf_underlying : (f : CuspForm 𝒮ℒ k) ≠ 0 := by
    intro h
    apply hf
    apply Subtype.ext
    exact h
  by_contra hcoeff
  push Not at hcoeff
  have hq : UpperHalfPlane.qExpansion 1
      (CuspForm.toModularFormₗ (f : CuspForm 𝒮ℒ k)) = 0 := by
    apply PowerSeries.ext
    intro n
    change complexCoeffs f n = 0
    exact hcoeff n
  have hmf : CuspForm.toModularFormₗ (f : CuspForm 𝒮ℒ k) = 0 :=
    (ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL
      (CuspForm.toModularFormₗ (f : CuspForm 𝒮ℒ k))).mp hq
  apply hf_underlying
  apply CuspForm.toModularFormₗ_injective
  simpa using hmf

private lemma L_eq_LSeries_on_right_halfPlane (hk : 0 < k) (f : RealCuspForm k) :
    {s : ℂ | (k : ℝ) / 2 + 1 < s.re}.EqOn
      (ModularForm.L hk (f : CuspForm 𝒮ℒ k)) (_root_.LSeries (complexCoeffs f)) := by
  intro s hs
  have hsum : HasSum (fun n ↦ complexCoeffs f n / (n : ℂ) ^ s)
      (ModularForm.L hk (f : CuspForm 𝒮ℒ k) s) := by
    simpa [complexCoeffs, Subgroup.strictWidthInfty_SL2Z] using
      CuspForm.hasSum_L hk (f : CuspForm 𝒮ℒ k) hs
  calc
    ModularForm.L hk (f : CuspForm 𝒮ℒ k) s =
        ∑' n, complexCoeffs f n / (n : ℂ) ^ s := hsum.tsum_eq.symm
    _ = _root_.LSeries (complexCoeffs f) s :=
      (LSeries_def₀ (complexCoeffs_zero f) s).symm

private theorem exists_coeff_neg_aux (hk : 0 < k) (f : RealCuspForm k) (hf : f ≠ 0) :
    ∃ n, coeff f n < 0 := by
  by_contra hneg
  push Not at hneg
  have hnonneg : 0 ≤ complexCoeffs f := fun n ↦ by
    rw [Complex.le_def]
    exact ⟨hneg n, (f.property n).symm⟩
  obtain ⟨n, hn⟩ := exists_complexCoeff_ne_zero hf
  have hn0 : n ≠ 0 := by
    intro hn_zero
    subst n
    exact hn (complexCoeffs_zero f)
  have hpos : ∃ n, n ≠ 0 ∧ 0 < complexCoeffs f n := by
    exact ⟨n, hn0, lt_of_le_of_ne (hnonneg n) (Ne.symm hn)⟩
  let x : ℝ := (k : ℝ) / 2
  have hO : complexCoeffs f =O[Filter.atTop] fun n ↦ (n : ℝ) ^ x := by
    change (fun n ↦ (UpperHalfPlane.qExpansion 1 (f : CuspForm 𝒮ℒ k)).coeff n) =O[
      Filter.atTop] fun n ↦ (n : ℝ) ^ x
    simpa [x, Subgroup.strictWidthInfty_SL2Z] using
      CuspFormClass.qExpansion_isBigO (f : CuspForm 𝒮ℒ k)
  have habscissa : LSeries.abscissaOfAbsConv (complexCoeffs f) ≤ ((x + 1 : ℝ) : EReal) := by
    simpa using LSeries.abscissaOfAbsConv_le_of_isBigO_rpow hO
  have hLpos : 0 < ModularForm.L hk (f : CuspForm 𝒮ℒ k) (0 : ℝ) :=
    Section4.LSeriesPositivity.positive_of_differentiable_of_eqOn_of_exists_pos
      (x := x + 1) hnonneg hpos
      (CuspForm.differentiable_L hk (f : CuspForm 𝒮ℒ k)) habscissa
      (by simpa [x] using L_eq_LSeries_on_right_halfPlane hk f) 0
  have hLzero : ModularForm.L hk (f : CuspForm 𝒮ℒ k) 0 = 0 := by
    simp [ModularForm.L, Complex.Gammaℂ_def, Complex.Gamma_zero]
  change 0 < ModularForm.L hk (f : CuspForm 𝒮ℒ k) 0 at hLpos
  rw [hLzero] at hLpos
  exact (lt_irrefl (0 : ℂ)) hLpos

/-- Every nonzero real level-one cusp form of positive weight has a negative Fourier
coefficient at a positive index. -/
theorem exists_coeff_neg (hk : 0 < k) (f : RealCuspForm k) (hf : f ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ coeff f n < 0 := by
  obtain ⟨n, hn⟩ := exists_coeff_neg_aux hk f hf
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
  exact ⟨n, Nat.pos_of_ne_zero hn0, hn⟩

/-- A real level-one cusp form with coefficientwise-nonnegative q-expansion is zero. -/
theorem eq_zero_of_coeff_nonneg (hk : 0 < k) (f : RealCuspForm k)
    (hnonneg : ∀ n, 0 ≤ coeff f n) :
    f = 0 := by
  by_contra hf
  obtain ⟨n, _, hn⟩ := exists_coeff_neg hk f hf
  exact (not_lt_of_ge (hnonneg n)) hn

namespace Coordinates

/-- Task 3's directional-detection hypothesis for the coordinate coefficient functionals. -/
theorem exists_coeffContinuous_neg (hk : 0 < k) (v : Coordinates.Space k) (hv : v ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ Coordinates.coeffContinuous n v < 0 := by
  have hform : Coordinates.toForm k v ≠ 0 := by
    intro h
    apply hv
    exact (Coordinates.toForm k).injective (h.trans (map_zero (Coordinates.toForm k)).symm)
  simpa using exists_coeff_neg hk (Coordinates.toForm k v) hform

/-- The directional-detection hypothesis in exactly the form consumed by the generic
finite-half-space theorem. -/
theorem detects_nonzero_direction (hk : 0 < k) :
    ∀ v : Coordinates.Space k, v ≠ 0 →
      ∃ n : ℕ, Coordinates.coeffContinuous n v < 0 := by
  intro v hv
  obtain ⟨n, _, hn⟩ := exists_coeffContinuous_neg hk v hv
  exact ⟨n, hn⟩

end Coordinates

end Section4.RealForms.RealCuspForm
