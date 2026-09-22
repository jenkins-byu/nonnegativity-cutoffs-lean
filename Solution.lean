import Section4

/-!
# Proved Palomar solution

This module restates the small declaration from `Challenge.lean` and proves it from the full
Section 4 development.  Comparator checks that the Challenge and Solution declarations have
exactly the same name and type.
-/

open scoped MatrixGroups UpperHalfPlane

open UpperHalfPlane
open Section4.RealForms

/-- For every level-one weight `k ≥ 12` divisible by four, there is a positive inclusive
nonnegativity cutoff which is also the greatest possible first negative Fourier-coefficient
index among level-one modular forms with real Fourier coefficients. -/
theorem NonnegativeModularForms.exists_optimal_nonnegativity_cutoff
    (k : ℕ) (hk12 : 12 ≤ k) (hk4 : k % 4 = 0) :
    ∃ A : ℕ, 0 < A ∧
      (∀ f : ModularForm 𝒮ℒ (k : ℤ),
        (∀ n : ℕ, ((qExpansion 1 (f : ℍ → ℂ)).coeff n).im = 0) →
        (∀ n : ℕ, n ≤ A → 0 ≤ ((qExpansion 1 (f : ℍ → ℂ)).coeff n).re) →
        ∀ n : ℕ, 0 ≤ ((qExpansion 1 (f : ℍ → ℂ)).coeff n).re) ∧
      (∃ f : ModularForm 𝒮ℒ (k : ℤ),
        (∀ n : ℕ, ((qExpansion 1 (f : ℍ → ℂ)).coeff n).im = 0) ∧
        ((qExpansion 1 (f : ℍ → ℂ)).coeff A).re < 0 ∧
        ∀ m : ℕ, m < A → 0 ≤ ((qExpansion 1 (f : ℍ → ℂ)).coeff m).re) ∧
      ∀ n : ℕ,
        (∃ f : ModularForm 𝒮ℒ (k : ℤ),
          (∀ m : ℕ, ((qExpansion 1 (f : ℍ → ℂ)).coeff m).im = 0) ∧
          ((qExpansion 1 (f : ℍ → ℂ)).coeff n).re < 0 ∧
          ∀ m : ℕ, m < n → 0 ≤ ((qExpansion 1 (f : ℍ → ℂ)).coeff m).re) →
        n ≤ A := by
  have hkpos : 0 < k := by omega
  let A := NonnegativityBound.A k
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simpa [A] using NonnegativityBound.A_pos k
  · intro f hreal hinitial n
    let rf : RealModularForm (k : ℤ) := ⟨f, hreal⟩
    have hinitial' : ∀ m, m ≤ NonnegativityBound.A k →
        0 ≤ RealModularForm.coeff rf m := by
      intro m hm
      simpa [rf, RealModularForm.coeff, realQCoeffAt] using
        hinitial m (by simpa [A] using hm)
    have hall := NonnegativityBound.realModularForm_nonnegative_of_nonnegative_up_to_A
      k hkpos hk4 rf hinitial'
    simpa [rf, RealModularForm.coeff, realQCoeffAt] using hall n
  · have hgreatest :=
      NonnegativityBound.A_isGreatest_firstNegativeIndices_of_twelve_le
        k hkpos hk4 hk12
    rcases hgreatest.1 with ⟨rf, hfirst⟩
    refine ⟨rf.1, rf.property, ?_, ?_⟩
    · simpa [A, NonnegativityBound.FirstNegativeAt, RealModularForm.coeff,
        realQCoeffAt] using hfirst.1
    · intro m hm
      simpa [RealModularForm.coeff, realQCoeffAt] using
        hfirst.2 m (by simpa [A] using hm)
  · intro n hn
    rcases hn with ⟨f, hreal, hnegative, hprevious⟩
    let rf : RealModularForm (k : ℤ) := ⟨f, hreal⟩
    have hfirst : NonnegativityBound.FirstNegativeAt rf n := by
      constructor
      · simpa [rf, RealModularForm.coeff, realQCoeffAt] using hnegative
      · intro m hm
        simpa [rf, RealModularForm.coeff, realQCoeffAt] using hprevious m hm
    have hle := NonnegativityBound.firstNegativeAt_le_A k hkpos hk4 hfirst
    simpa [A] using hle
