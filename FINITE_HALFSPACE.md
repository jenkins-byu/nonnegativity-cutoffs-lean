# Task 3: generic finite-half-space theorem

Date: 2026-08-18

## Result

The abstract finite-dimensional argument planned for Section 4 is fully formalized and compiles
in the pinned project. It is independent of modular forms and makes no nonemptiness assumption on
the feasible set.

Let `V` be a finite-dimensional real normed vector space, let

```lean
e : ℕ → ℝ
b : ℕ → V →L[ℝ] ℝ
```

and put

```lean
halfspace e b n = {v | 0 ≤ e n + b n v}
finiteIntersection e b I = {v | ∀ n ∈ I, v ∈ halfspace e b n}
fullIntersection e b = {v | ∀ n, v ∈ halfspace e b n}.
```

The two substantive hypotheses are:

```lean
hdetect : ∀ v : V, v ≠ 0 → ∃ n, b n v < 0
```

and

```lean
htail : ∀ R : ℝ, 0 ≤ R →
  ∀ᶠ n in Filter.atTop,
    Metric.closedBall (0 : V) R ⊆ halfspace e b n.
```

The first says that the homogeneous inequalities have no common nonzero direction. The second
says that on each fixed bounded region every sufficiently late affine inequality is automatic.

## Main public statements

The finite-set form is:

```lean
theorem exists_finite_reduction [FiniteDimensional ℝ V]
    (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (hdetect : ∀ v : V, v ≠ 0 → ∃ n, b n v < 0)
    (htail : EventuallyContainsClosedBalls e b) :
    ∃ I : Finset ℕ,
      Bornology.IsBounded (finiteIntersection e b I) ∧
        finiteIntersection e b I = fullIntersection e b
```

The initial-segment form, intended to support the definition of a least cutoff, is:

```lean
theorem exists_initialSegment_reduction [FiniteDimensional ℝ V]
    (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (hdetect : ∀ v : V, v ≠ 0 → ∃ n, b n v < 0)
    (htail : EventuallyContainsClosedBalls e b) :
    ∃ N : ℕ,
      Bornology.IsBounded (finiteIntersection e b (Finset.range N)) ∧
        finiteIntersection e b (Finset.range N) = fullIntersection e b
```

Here `Finset.range N` means the indices `n < N`. If the paper's convention uses inequalities
through index `A`, the Lean initial segment is therefore `Finset.range (A + 1)`.

There is also a packaged geometric form:

```lean
theorem exists_compact_finite_reduction ... :
    ∃ I : Finset ℕ,
      IsCompact (finiteIntersection e b I) ∧
        Convex ℝ (finiteIntersection e b I) ∧
          finiteIntersection e b I = fullIntersection e b
```

## Proof formalized in Lean

1. For each index `n`, take the open subset of the unit sphere on which `b n v < 0`.
   `hdetect` says these sets cover the sphere.

2. Compactness of the sphere supplies a finite subcover. The proof inserts index `0` into this
   finite set so that the finite minimum below is always defined, even when the sphere is empty.

3. On the sphere, take the minimum of the selected functionals. This is continuous by
   `Continuous.finset_inf'_apply` and is strictly negative at every sphere point.

4. `IsCompact.exists_forall_le'` supplies a uniform `δ > 0` such that at every unit vector one
   selected functional is at most `-δ`. This API also handles an empty sphere, so no nontriviality
   assumption on `V` is exposed.

5. The sum of the absolute values of the finitely many constants `e n` bounds all their offsets.
   Normalizing any nonzero point in the finite affine intersection then gives an explicit norm
   bound. Thus some finite subintersection is bounded.

6. Enclose that bounded subintersection in a closed ball. The eventual-ball hypothesis gives an
   index `N` after which every half-space contains the ball. Adjoining `Finset.range N` to the
   finite obstructing set gives a finite intersection equal to the full one.

7. Every finite set of natural indices is contained in some `Finset.range N`, yielding the
   initial-segment version. Closedness, boundedness, and finite-dimensional properness yield
   compactness; convexity is proved directly from the affine inequalities.

## Edge cases and design choices

- The zero-dimensional case is internal to the proof. No `[Nontrivial V]` assumption is needed.
- The feasible set may be empty. No base point or normalization such as `a(0) = 1` is assumed.
- The index type is `ℕ`, as approved. Later modular-form code can encode the paper's positive
  coefficient indices by shifting indices or by proving that the index-zero inequality is
  harmless.
- The theorem uses continuous linear functionals. This makes compactness and continuity explicit
  and will remain suitable for finite-dimensional higher-level spaces.
- No custom `Polytope` structure is introduced. The output is an equality of sets together with
  the standard mathlib predicates `IsBounded`, `IsCompact`, and `Convex`.
- The abstract theorem does not mention a modular-form basis, a dimension formula, level one, or
  a weight. Those enter only in later specialization tasks.

## Downstream contract

To specialize this theorem to Section 4, later tasks must provide:

1. a finite-dimensional real normed space representing the real cusp-form directions;
2. continuous real-linear coefficient functionals `b n`;
3. constants `e n` coming from the Eisenstein-series coefficients;
4. `hdetect`, supplied by the Task 2 sign-change theorem after connecting the representation to
   q-expansion coefficients; and
5. `htail`, supplied by the coefficient-growth comparison used in Section 4.

No modular specialization has been started in Task 3.

## Verification

- Source: `Section4/FiniteHalfspace.lean`.
- The library root `Section4.lean` imports this source.
- The file contains no `sorry`, `admit`, or added axiom.
- Verification command: `.\lake.ps1 build`.
