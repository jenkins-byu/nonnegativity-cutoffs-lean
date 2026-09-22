import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# A nonnegativity cutoff for level-one modular forms

This file isolates the statement intended for Palomar review. It uses Mathlib's level-one modular
forms and q-expansion coefficients directly.

For every weight `k ≥ 12` divisible by four, the theorem shows that there is a positive integer
`A`, depending on `k`, with the following properties for level-one modular forms of weight `k` with
real Fourier coefficients:

* if the Fourier coefficients of `q^0, ..., q^A` are nonnegative, then every Fourier coefficient
  is nonnegative;
* some such form has all earlier Fourier coefficients nonnegative and its coefficient of `q^A`
  negative; and
* whenever such a form has all Fourier coefficients with indices less than `n` nonnegative and its
  coefficient of `q^n` negative, one has `n ≤ A`.

Thus `A` is a finite nonnegativity cutoff and the largest possible index at which a Fourier
coefficient can become negative for the first time.
-/

open scoped MatrixGroups UpperHalfPlane

open UpperHalfPlane

/-- For every weight `k ≥ 12` divisible by four, there is a positive integer `A`, depending on `k`,
such that any level-one modular form of weight `k` with real Fourier coefficients has all Fourier
coefficients nonnegative if its coefficients of `q^0, ..., q^A` are nonnegative. Some such form has
all earlier Fourier coefficients nonnegative and its coefficient of `q^A` negative. Moreover,
whenever such a form has all Fourier coefficients with indices less than `n` nonnegative and its
coefficient of `q^n` negative, one has `n ≤ A`. -/
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
  sorry
