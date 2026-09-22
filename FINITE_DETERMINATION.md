# Task 9: finite determination and Section 4 well-definedness

Date completed: 2026-08-21

## Result

Task 9 is complete. The project now specializes the generic finite-half-space theorem to the
normalized real level-one modular-form slice in every positive weight `k` divisible by four.
It proves the bounded finite convex-polytope statement corresponding to Theorem 5 of the paper,
a finite coefficient test using only positive indices, and an initial-segment nonnegativity bound.

The production implementation is `Section4/FiniteDetermination.lean`, under the namespace
`Section4.RealForms.FiniteDetermination`.

The principal user-facing theorem is:

```lean
theorem exists_nonnegativity_bound_levelOne (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    ∃ N : ℕ, ∀ f : NormalizedRealModularForm (k : ℤ),
      (∀ n, 1 ≤ n → n ≤ N → 0 ≤ NormalizedRealModularForm.coeff f n) →
        ∀ n, 0 ≤ NormalizedRealModularForm.coeff f n
```

Thus, for each admissible weight there is a uniform finite cutoff: if a normalized real
level-one modular form has nonnegative coefficients through that cutoff, all of its coefficients
are nonnegative. This is the agreed formal well-definedness statement for the nonnegativity bound.

## Exact affine-slice parametrization

Task 6 associated a cusp-coordinate vector to every normalized form. Task 9 constructs the
inverse map explicitly:

```lean
formOfCoordinates v = E_k + g_v.
```

The constant coefficient is one because `E_k` has constant coefficient one and `g_v` is cuspidal.
The project proves both inverse identities and packages them as

```lean
normalizedFormsEquivCoordinates ... :
  NormalizedRealModularForm (k : ℤ) ≃
    RealCuspForm.Coordinates.Space (k : ℤ)
```

This establishes that the Euclidean space used in the geometric argument parametrizes the entire
normalized real affine slice, rather than merely receiving a map from it.

For every vector `v` and index `n`, the coefficient formula is

```lean
theorem coeff_formOfCoordinates ... :
  NormalizedRealModularForm.coeff (formOfCoordinates ... v) n =
    EisensteinDecomposition.eisensteinCoeff ... n +
      RealCuspForm.Coordinates.coeffContinuous n v
```

Consequently, membership in the `n`th coordinate half-space is definitionally the same
coefficient inequality used in the paper.

## The coordinate set and its geometry

The full feasible set is defined as

```lean
nonnegativeCoordinates ... =
  FiniteHalfspace.fullIntersection eisensteinCoeff coeffContinuous.
```

The bridge back to modular forms is:

```lean
theorem cuspCoordinates_mem_nonnegativeCoordinates_iff ... (f : ...) :
  cuspCoordinates ... f ∈ nonnegativeCoordinates ... ↔
    ∀ n, 0 ≤ NormalizedRealModularForm.coeff f n
```

The project separately exports closedness, convexity, boundedness, and compactness of this set.
Boundedness and compactness use Task 5's theorem that every nonzero cusp direction has a negative
coefficient. Convexity and closedness come from the generic affine-half-space construction.

## Bounded finite convex polytope

The theorem corresponding most closely to Theorem 5 is:

```lean
theorem exists_bounded_finite_convex_polytope ... :
  ∃ A : Finset ℕ,
    (∀ n ∈ A, 0 < n) ∧
    Bornology.IsBounded (finiteNonnegativeCoordinates ... A) ∧
    IsCompact (finiteNonnegativeCoordinates ... A) ∧
    Convex ℝ (finiteNonnegativeCoordinates ... A) ∧
    finiteNonnegativeCoordinates ... A = nonnegativeCoordinates ...
```

Its two substantive inputs are exactly the interfaces prepared earlier:

1. `RealCuspForm.Coordinates.detects_nonzero_direction` from Task 5;
2. `EisensteinDomination.eventuallyContainsClosedBalls` from Task 8.

The generic theorem initially permits index zero because its index type is `ℕ`. Task 9 proves
that the index-zero half-space contains every coordinate vector: the normalized Eisenstein
constant is one and every cusp constant coefficient is zero. It therefore erases zero from the
finite witness and proves the intersection unchanged. The final finite set consists entirely of
positive integers, as in the paper.

No bespoke `Polytope` structure is introduced. Here “bounded finite convex polytope” means exactly
a bounded and convex set represented as the intersection of finitely many closed affine
half-spaces; compactness is also recorded using mathlib's standard predicate.

## Finite and initial-segment coefficient tests

The positive-index finite-set form is:

```lean
theorem exists_finite_coefficient_test_levelOne ... :
  ∃ A : Finset ℕ,
    (∀ n ∈ A, 0 < n) ∧
    ∀ f : NormalizedRealModularForm (k : ℤ),
      ((∀ n ∈ A, 0 ≤ f.coeff n) ↔ ∀ n, 0 ≤ f.coeff n)
```

The initial-segment form is slightly stronger than the one-way public statement:

```lean
theorem exists_initial_coefficient_test_levelOne ... :
  ∃ N : ℕ, ∀ f : NormalizedRealModularForm (k : ℤ),
    ((∀ n, 1 ≤ n → n ≤ N → 0 ≤ f.coeff n) ↔
      ∀ n, 0 ≤ f.coeff n)
```

The returned endpoint is inclusive. It need not be the least possible endpoint. The proof is
qualitative and noncomputable because the compactness argument and asymptotic cusp estimates do
not produce numerical thresholds.

The contrapositive interpretation is also exported:

```lean
theorem exists_bounded_negative_witness_levelOne ... :
  ∃ N : ℕ, ∀ f : NormalizedRealModularForm (k : ℤ),
    (∃ n, f.coeff n < 0) →
      ∃ n, 1 ≤ n ∧ n ≤ N ∧ f.coeff n < 0
```

This says directly that first-negative-coefficient phenomena cannot escape to arbitrarily large
indices within a fixed normalized weight.

## Relation to the symbol `A(k)`

This Task 9 file proves the substantive existence input in the approved finite-test form. Task 10
uses it in `Section4/NonnegativityBound.lean` to define `A(k)` noncomputably as the least positive
successful inclusive cutoff. Task 10 then proves detection, minimality, first-negative-index
maximality, and the arbitrary-real-form version. See `NONNEGATIVITY_BOUND.md` for the exact public
interface and indexing convention.

The present theorem is stated for the bundled type `NormalizedRealModularForm`, so coefficientwise
reality and constant coefficient one are enforced by the type rather than repeated as hypotheses.
It does not make a statement about modular forms with genuinely complex coefficients.

## Generalization boundary

The final assembly has a clean dependency split:

- the coordinate equivalence and coefficient functionals describe the normalized affine slice;
- the sign-change theorem blocks nonzero homogeneous directions;
- the Eisenstein/cusp exponent comparison makes late inequalities automatic on bounded sets;
- the generic finite-dimensional theorem supplies finite reduction.

For a later weight-2 prime-level project, the abstract geometry can be reused unchanged. The
level-dependent work will be constructing the correct real normalized affine slice and proving
analogues of the directional and uniform-tail inputs. The Task 9 specialization itself is short
because those boundaries were kept explicit in Tasks 3–8.

## Verification

- Production source: `Section4/FiniteDetermination.lean`.
- The library root `Section4.lean` imports the production source.
- The production source has no linter warnings.
- The project contains no `sorry`, `admit`, or declared axiom.
- Verification command: `.\lake.ps1 build`.
