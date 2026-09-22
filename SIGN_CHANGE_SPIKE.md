# Task 2: sign-change feasibility spike

Date: 2026-08-18

> **Task 5 update.** The generalized L-series lemmas now live in the production module
> `Section4/LSeriesPositivity.lean`, and the invariant public sign-change theorem lives in
> `Section4/RealCuspSignChange.lean`. The spike continues to compile as a regression theorem with
> its original raw `Complex.im` interface.

## Result

The proposed analytic proof is fully feasible in the pinned Lean project. The complete theorem
compiles; there is no remaining mathematical or API gap.

The spike proves the following statement for every positive integral weight, without assuming
that the weight is even or divisible by four:

```lean
theorem exists_cuspCoeff_re_neg
    {k : ℤ} (hk : 0 < k) (f : CuspForm 𝒮ℒ k) (hf : f ≠ 0)
    (hreal : ∀ n, (cuspCoeffs f n).im = 0) :
    ∃ n, (cuspCoeffs f n).re < 0
```

It also proves the form that will feed directly into the convex-geometric argument:

```lean
theorem eq_zero_of_cuspCoeffs_re_nonneg
    {k : ℤ} (hk : 0 < k) (f : CuspForm 𝒮ℒ k)
    (hreal : ∀ n, (cuspCoeffs f n).im = 0)
    (hnonneg : ∀ n, 0 ≤ (cuspCoeffs f n).re) :
    f = 0
```

Thus the homogeneous coefficient half-spaces have intersection `{0}` on the real cusp-form
space, exactly as required in Section 4.

## Exact proof accepted by Lean

Let `a n` be the `n`th coefficient of the q-expansion of `f` at width `1`.

1. Suppose, toward a contradiction, that no real coefficient is negative. Because every
   coefficient has zero imaginary part, Lean's `ComplexOrder` converts this into the pointwise
   complex inequality `0 ≤ a`.

2. If every coefficient were zero, `PowerSeries.ext` would make the q-expansion zero.
   `ModularForm.qExpansion_eq_zero_iff`, applied after the inclusion
   `CuspForm.toModularFormₗ`, would then give `f = 0`. Hence a nonzero `f` has some nonzero
   coefficient.

3. `CuspFormClass.qExpansion_coeff_zero` says `a 0 = 0`, so that nonzero coefficient occurs at
   an index `n ≠ 0`.

4. Since `a n` is nonnegative and nonzero, it is strictly positive. Consequently there is a
   nonzero index with `0 < a n`.

5. `CuspFormClass.qExpansion_isBigO` gives
   `a(n) = O(n^(k/2))`. Then
   `LSeries.abscissaOfAbsConv_le_of_isBigO_rpow` proves that the abscissa of absolute convergence
   is at most `k/2 + 1`.

6. `CuspForm.hasSum_L`, together with `Subgroup.strictWidthInfty_SL2Z`, identifies the modular
   L-function with the Dirichlet L-series on `re(s) > k/2 + 1`. The conversion from its raw
   summand to `LSeries` uses `LSeries_def₀` and the already established equality `a 0 = 0`.

7. `CuspForm.differentiable_L` proves that `ModularForm.L hk f` is entire.

8. The spike generalizes mathlib's `LSeries.positive_of_differentiable_of_eqOn`. Mathlib assumes
   `0 < a 1`; the local theorem assumes only
   `∃ n, n ≠ 0 ∧ 0 < a n`. Its proof is otherwise the same: positivity in the half-plane of
   convergence comes from the positive term at that index, and alternating signs of all
   derivatives propagate positivity along the real axis through the entire continuation.
   Applying this at `s = 0` gives `0 < ModularForm.L hk f 0`.

9. Unfolding `ModularForm.L` and `Complex.Gammaℂ_def`, and using `Complex.Gamma_zero`, proves
   `ModularForm.L hk f 0 = 0`. This contradicts the preceding strict positivity.

## The local L-series generalization

Two reusable lemmas were required:

```lean
positive_of_exists_pos
positive_of_differentiable_of_eqOn_of_exists_pos
```

The only change from the existing mathlib lemmas is replacing the witness at index `1` by a
witness at an arbitrary nonzero index. At the base point in the convergence half-plane,
`Summable.tsum_pos` accepts that arbitrary index and `LSeries.term_pos` uses the proof that the
index is nonzero. The analytic-continuation argument then copies mathlib's existing proof.

These lemmas are plausible upstream additions to mathlib, but keeping them locally does not
create a maintenance or trust problem.

## Where level one enters

The analytic argument itself is nearly level-independent. Level one is used in two concrete
places:

1. q-expansion injectivity is invoked at period `1` using `one_mem_strictPeriods_SL`;
2. `Subgroup.strictWidthInfty_SL2Z` simplifies the factor in `CuspForm.hasSum_L` to `1`.

At higher level, `CuspForm.hasSum_L` gives the Dirichlet series as
`strictWidthInfty^(-s) * L(f,s)`. Since the strict width is positive, the same strategy should
apply to that entire product, which also vanishes at zero. That extension was not implemented in
this level-one spike.

## Representation of real forms

For the spike, “real q-expansion” is the explicit hypothesis

```lean
∀ n, (cuspCoeffs f n).im = 0
```

The eventual public real cusp-form subspace should store this property, so the public sign-change
theorem will quantify over a real cusp form and will not display `Complex.im`. The proof above can
then be reused almost verbatim.

## Consequences for the project

- The sign-change input is no longer a feasibility risk.
- The project can prove the input invoked in Section 4 rather than assume it.
- The homogeneous intersection statement needed for the compact-sphere argument already has a
  compiled form.
- No Hecke eigenform decomposition, Deligne bound, Poincare series, or explicit basis is used.
- The only analytic coefficient bound needed here is mathlib's existing `O(n^(k/2))` bound.

## Verification

- Source: `Section4/SignChangeSpike.lean`.
- The spike contains no `sorry`, `admit`, or added axiom.
- `.\lake.ps1 build Section4.SignChangeSpike` completes successfully: 3143 jobs.
