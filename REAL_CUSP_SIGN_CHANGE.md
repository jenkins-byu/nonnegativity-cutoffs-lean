# Task 5: sign change for real cusp forms

Date: 2026-08-18

## Result

The Task 2 feasibility proof has been promoted into the stable project API. The reusable L-series
generalization is separated from modular forms, and the public cusp-form theorems now quantify over
`RealCuspForm` rather than exposing a family of raw `Complex.im` hypotheses.

The original spike remains compiled as a regression theorem.

## Stable L-series generalization

`Section4/LSeriesPositivity.lean` proves:

```lean
lemma positive_of_exists_pos {a : ℕ → ℂ} (ha₀ : 0 ≤ a)
    (ha_pos : ∃ n, n ≠ 0 ∧ 0 < a n) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) :
    0 < LSeries a x
```

and its analytic-continuation form:

```lean
lemma positive_of_differentiable_of_eqOn_of_exists_pos {a : ℕ → ℂ}
    (ha₀ : 0 ≤ a)
    (ha_pos : ∃ n, n ≠ 0 ∧ 0 < a n)
    (hf : Differentiable ℂ f)
    (hx : LSeries.abscissaOfAbsConv a ≤ x)
    (hf' : {s | x < s.re}.EqOn f (LSeries a)) (y : ℝ) :
    0 < f y
```

These differ from the corresponding mathlib lemmas only in allowing the strictly positive
coefficient to occur at an arbitrary nonzero index rather than requiring it at index `1`.

## Public sign-change API

For every positive integral weight, the production theorem is:

```lean
theorem RealCuspForm.exists_coeff_neg
    (hk : 0 < k) (f : RealCuspForm k) (hf : f ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ RealCuspForm.coeff f n < 0
```

The positive-index conclusion is part of the theorem. It follows because the constant coefficient
of a cusp form is zero.

The zero-detection form is:

```lean
theorem RealCuspForm.eq_zero_of_coeff_nonneg
    (hk : 0 < k) (f : RealCuspForm k)
    (hnonneg : ∀ n, 0 ≤ RealCuspForm.coeff f n) :
    f = 0
```

Neither theorem mentions complex coefficients, imaginary parts, a chosen basis, or Euclidean
coordinates.

## Coordinate interface for Task 3

The sign-change theorem is transported through the noncomputable coordinate equivalence from
Task 4. The strongest exported form retains positivity of the index:

```lean
RealCuspForm.Coordinates.exists_coeffContinuous_neg
```

The exact hypothesis required by `FiniteHalfspace.exists_finite_reduction` is packaged as:

```lean
theorem RealCuspForm.Coordinates.detects_nonzero_direction (hk : 0 < k) :
    ∀ v : Coordinates.Space k, v ≠ 0 →
      ∃ n : ℕ, Coordinates.coeffContinuous n v < 0
```

Thus the directional-obstruction half of the eventual application of Task 3 is now completely
discharged.

## Analytic proof

The proof retains the route verified in Task 2:

1. Assume every real coefficient is nonnegative. The stored reality property turns this into
   nonnegativity in mathlib's order on complex numbers.
2. Q-expansion injectivity gives a nonzero coefficient; the zero constant term makes its index
   nonzero. Nonnegativity then makes that coefficient strictly positive.
3. `CuspFormClass.qExpansion_isBigO` bounds the coefficients by `O(n^(k/2))`, giving the required
   bound on the abscissa of absolute convergence.
4. `CuspForm.hasSum_L` identifies the modular L-function with the coefficient L-series in the
   right half-plane. The level-one cusp-width identity removes the scaling factor.
5. The stable generalized positivity lemma and the entire continuation supplied by
   `CuspForm.differentiable_L` imply positivity at `s = 0`.
6. The reciprocal archimedean Gamma factor gives `L(f,0) = 0`, a contradiction.

No Hecke eigenbasis, Deligne bound, Poincare series, or explicit cusp-form basis is used.

## Scope

This task does not address Eisenstein coefficients, the normalized Eisenstein-cusp decomposition,
or uniformity of coefficient bounds on coordinate balls. Those remain Tasks 6–8.

The theorem assumes only `0 < k`; divisibility by four is not needed for the cusp sign-change
argument.

## Verification

- Stable sources: `Section4/LSeriesPositivity.lean` and
  `Section4/RealCuspSignChange.lean`.
- Regression source: `Section4/SignChangeSpike.lean`.
- All three are imported, directly or transitively, by `Section4.lean`.
- The sources contain no `sorry`, `admit`, or added axiom.
- Verification command: `.\lake.ps1 build`.
