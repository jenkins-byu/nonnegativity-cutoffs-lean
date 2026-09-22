# Task 7: Eisenstein positivity and qualitative lower growth

Date completed: 2026-08-21

## Result

Task 7 is complete. For every natural-number weight `k` satisfying

```lean
hkpos : 0 < k
hk4   : k % 4 = 0
```

and every positive index `n`, the project proves that the normalized level-one Eisenstein
coefficient is positive and satisfies

\[
\left(-\frac{2k}{B_k}\right)n^{k-1}
  \le a_{E_k}(n),
\qquad -\frac{2k}{B_k}>0.
\]

The real-power version of this inequality matches the form of mathlib's cusp-coefficient growth
theorem. The project also proves the strict exponent gap

\[
\frac{k}{2}<k-1.
\]

Consequently, Task 7 supplies all Eisenstein-side input needed to compare these coefficients with
a cusp bound of order `O(n^(k/2))`. Making that cusp estimate uniform over bounded coordinate sets
is deliberately left to Task 8.

The implementation is in `Section4/EisensteinPositivity.lean`, under the namespace
`Section4.RealForms.EisensteinPositivity`.

## Bernoulli sign

Mathlib does not provide a named general sign theorem for the Bernoulli convention used in the
Eisenstein q-expansion. The project therefore proves:

```lean
theorem bernoulli_neg (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
  bernoulli k < 0
```

The proof is not based on a finite table of Bernoulli values. From `4 ∣ k`, write `k = 4m` with
`m ≠ 0`. Mathlib's `hasSum_zeta_nat`, applied with exponent parameter `2m`, identifies the
strictly positive series

\[
\sum_{n\ge0}\frac{1}{n^{4m}}
\]

with Euler's expression involving `B_(4m)`. The term at `n=1` is positive and all terms are
nonnegative, so the sum is strictly positive. In Euler's expression the sign factor is
`(-1)^(2m+1) = -1`, while the powers of `2` and `π` and the reciprocal factorial are positive.
It follows that `B_(4m) < 0`.

This proof fixes the sign convention by using the same mathlib Bernoulli number that occurs in
`EisensteinSeries.E_qExpansion_coeff`.

## Positive normalization scale

The fixed coefficient scale is defined by

```lean
noncomputable def eisensteinScale (k : ℕ) : ℝ :=
  -(2 * (k : ℝ) / (bernoulli k : ℝ))
```

and its sign is exported as

```lean
theorem eisensteinScale_pos ... : 0 < eisensteinScale k
```

This isolates all Bernoulli-sign reasoning from subsequent coefficient and asymptotic arguments.

## Exact coefficient formula and positivity

For `n ≠ 0`, the real coefficient from Task 6 is identified with the divisor-sum formula:

```lean
theorem eisensteinCoeff_eq_scale_mul_sigma ... (n : ℕ) (hn : n ≠ 0) :
  EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n =
    eisensteinScale k * (ArithmeticFunction.sigma (k - 1) n : ℝ)
```

This follows directly from `EisensteinSeries.E_qExpansion_coeff`; no additional normalization
identity is assumed. Since `ArithmeticFunction.sigma_pos` gives strict positivity at every
nonzero index, the public positivity theorem is:

```lean
theorem eisensteinCoeff_pos ... (n : ℕ) (hn : 0 < n) :
  0 < EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n
```

## Divisor-sum lower bound

The elementary arithmetic input is formalized independently of modular forms:

```lean
theorem pow_le_sigma (a n : ℕ) (hn : n ≠ 0) :
  n ^ a ≤ ArithmeticFunction.sigma a n
```

After unfolding the divisor sum, the proof retains the summand indexed by the divisor `n` itself,
using `Nat.mem_divisors_self`. All other summands are nonnegative.

Multiplication by the nonnegative Eisenstein scale gives the natural-power bound:

```lean
theorem scale_mul_pow_le_eisensteinCoeff ... (n : ℕ) (hn : 0 < n) :
  eisensteinScale k * (n : ℝ) ^ (k - 1) ≤
    EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n
```

The corresponding real-power form is:

```lean
theorem scale_mul_rpow_le_eisensteinCoeff ... (n : ℕ) (hn : 0 < n) :
  eisensteinScale k * (n : ℝ) ^ ((k : ℝ) - 1) ≤
    EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n
```

The conversion uses `Real.rpow_natCast` and the fact that `1 ≤ k`.

## Qualitative downstream interface

Two final theorems make the Task 8 contract explicit:

```lean
theorem half_weight_lt_weight_sub_one ... :
  (k : ℝ) / 2 < (k : ℝ) - 1
```

and

```lean
theorem exists_pos_scale_rpow_le_eisensteinCoeff ... :
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
    c * (n : ℝ) ^ ((k : ℝ) - 1) ≤
      EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n
```

The existential form deliberately hides the exact Bernoulli normalization. Task 8 may use either
this qualitative theorem or the stronger explicit-scale theorem.

## Scope boundary

Task 7 proves only the Eisenstein side of the eventual domination argument. It does not:

- choose or inspect a cusp-form basis;
- turn pointwise cusp Big-O estimates into a uniform coordinate estimate;
- prove eventual nonnegativity on coordinate balls;
- apply the finite-half-space theorem.

Those are respectively the work of Tasks 8 and 9. No explicit numerical constant, canonical
basis, Deligne estimate, or Section 6 bound is used here.

## Verification

- Production source: `Section4/EisensteinPositivity.lean`.
- The library root `Section4.lean` imports the production source.
- The source has no linter warnings.
- The project contains no `sorry`, `admit`, or added axiom.
- Verification command: `.\lake.ps1 build`.
