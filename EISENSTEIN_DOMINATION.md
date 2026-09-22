# Task 8: Uniform Eisenstein domination on bounded coordinate sets

Date completed: 2026-08-21

## Result

Task 8 is complete. For every positive level-one weight `k` divisible by four, the project proves
the exact eventual-tail hypothesis required by the abstract finite-half-space theorem from Task 3:

```lean
theorem eventuallyContainsClosedBalls (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    FiniteHalfspace.EventuallyContainsClosedBalls
      (EisensteinDecomposition.eisensteinCoeff k hkpos hk4)
      (RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ)))
```

Unfolded, this says that for every real radius `R ≥ 0`, there is an index after which every
coordinate vector `v` with `‖v‖ ≤ R` satisfies

\[
0 \le a_{E_k}(n)+a_{g_v}(n).
\]

The index may depend on `R` and `k`, but it is uniform in `v`. This is the quantifier order needed
for the compactness and finite-reduction argument; a merely pointwise statement for each fixed
cusp form would not suffice.

The implementation is in `Section4/EisensteinDomination.lean`, under the namespace
`Section4.RealForms.EisensteinDomination`.

## Pointwise cusp growth

For an individual real cusp form, mathlib's complex q-expansion estimate is converted to a bound
on the real coefficient sequence:

```lean
theorem cuspCoeff_isBigO (k : ℕ) (f : RealCuspForm (k : ℤ)) :
  (fun n ↦ RealCuspForm.coeff f n) =O[atTop] cuspGrowth k
```

Here

```lean
cuspGrowth k n = (n : ℝ) ^ (((k : ℤ) : ℝ) / 2).
```

The proof applies `CuspFormClass.qExpansion_isBigO` to the underlying complex cusp form and uses
`Complex.abs_re_le_norm` to pass to real parts. It does not assume a Hecke eigenbasis, invoke
Deligne's sharper exponent, or introduce an unproved coefficient estimate.

## Finite-coordinate uniformization

Task 4 represents the real cusp space by the finite Euclidean space

```lean
Fin (RealCuspForm.Coordinates.dimension (k : ℤ)) → ℝ.
```

For its standard coordinate vector `e_i`, Task 8 defines `basisCoeff k i n` to be the `n`th
coefficient of the corresponding cusp form, and defines the finite envelope

\[
S_k(n)=\sum_i |a_{e_i}(n)|.
\]

Each basis sequence is `O(n^(k/2))`, so their finite absolute-value sum is also
`O(n^(k/2))`. Linearity and the sup norm on a finite function space give the explicit estimate

```lean
theorem abs_coeffContinuous_le_norm_mul_basisAbsSum ... :
  |RealCuspForm.Coordinates.coeffContinuous n v| ≤
    ‖v‖ * basisAbsSum k n
```

Thus a single scalar sequence controls every cusp coefficient on a coordinate ball. The proof is
valid in dimension zero as well: the coordinate sum is then empty and the envelope is zero.

The chosen basis is the standard basis of the noncanonical coordinate equivalence fixed in Task 4.
No arithmetic property of this basis is used. This separation is intentional: a future level or
weight generalization can replace the underlying finite-dimensional real cusp space and its
coordinate equivalence while reusing the finite-family argument.

## Exponent comparison and Eisenstein lower bound

Since an admissible weight is divisible by four, the real cusp exponent agrees with the natural
exponent `k / 2`, and

\[
k/2<k-1.
\]

Mathlib's polynomial little-oh theorem therefore yields

```lean
theorem basisAbsSum_isLittleO_eisensteinPower ... :
  basisAbsSum k =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (k - 1))
```

For a fixed `R ≥ 0`, little-oh is instantiated with the positive Task 7 normalization constant
`eisensteinScale k`. Combining the resulting eventual inequality with Task 7's lower bound gives

```lean
theorem eventually_radius_mul_basisAbsSum_le_eisensteinCoeff ... :
  ∀ᶠ n in atTop,
    R * basisAbsSum k n ≤
      EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n
```

The proof separately includes the eventual condition `0 < n`, exactly where Task 7's divisor-sum
lower bound requires a positive index.

## Uniform nonnegativity and the exported contract

For `v` in the closed ball of radius `R`, the coordinate estimate and the envelope inequality give

\[
|a_{g_v}(n)|\le a_{E_k}(n).
\]

In particular `-a_E(n) ≤ a_{g_v}(n)`, which proves the affine nonnegativity inequality. The
intermediate uniform statement is exported as

```lean
theorem eventually_nonneg_on_closedBall ... (R : ℝ) (hR : 0 ≤ R) :
  ∀ᶠ n in atTop, ∀ v : RealCuspForm.Coordinates.Space (k : ℤ),
    v ∈ closedBall 0 R →
      0 ≤ EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n +
        RealCuspForm.Coordinates.coeffContinuous n v
```

The final `eventuallyContainsClosedBalls` theorem is a direct packaging of this result into the
abstract predicate from Task 3. It can therefore be supplied to
`FiniteHalfspace.exists_finite_reduction` without any restatement or adapter lemma.

## Generalization boundary

The finite-coordinate part of Task 8 depends only on:

- a finite Euclidean coordinate model for the real cusp space;
- continuous linear coefficient functionals;
- a pointwise common-exponent Big-O theorem for each cusp form;
- a positive comparison term with strictly larger polynomial exponent.

Only the final comparison uses the level-one normalized Eisenstein coefficient and its explicit
Task 7 lower bound. This keeps the reusable finite-dimensional mechanism separate from the
level-one arithmetic input, which is the intended architecture for a later weight-2 prime-level
formalization.

## Scope boundary

Task 8 proves the eventual-tail condition but does not apply the finite-half-space theorem. In
particular, it does not yet:

- combine the tail theorem with the Task 5 directional sign obstruction;
- produce the finite set of coefficient indices;
- prove the final finite determination statement for the Section 4 nonnegative-coefficient set;
- identify an explicit numerical cutoff.

Those belong to Task 9. The theorem here is qualitative: it proves existence of an eventual index
for each radius rather than computing one, because mathlib's cusp Big-O theorem is itself
qualitative.

## Verification

- Production source: `Section4/EisensteinDomination.lean`.
- The library root `Section4.lean` imports the production source.
- The production source has no linter warnings.
- The project contains no `sorry`, `admit`, or added axiom.
- Verification command: `.\lake.ps1 build`.
