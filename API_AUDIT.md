# Task 1 API audit for Section 4 and final resolution

Date of audit: 2026-08-18

Final resolution: 2026-08-24

Sections 1-7 preserve the original Task 1 audit and therefore sometimes use future tense. Every
required local development identified there has now been implemented. Section 8 records the
final production interfaces, dependency decisions, and verification status.

## 1. Scope and result

The target is Theorem 5 in Section 4 of Jenkins--Rouse: for fixed positive
`k ≡ 0 (mod 4)`, the normalized level-one forms with nonnegative real Fourier coefficients form a
bounded set cut out by finitely many coefficient half-spaces. In particular, some finite set of
positive indices detects coefficientwise nonnegativity, and hence `A(k)` is well-defined.

The result of this audit is **feasible, but not a short assembly of existing theorems**. Mathlib
now supplies the central modular-form analytic input, including the entire continuation of the
ordinary L-function of a cusp form. It also supplies q-expansions, the Eisenstein coefficient
formula, level-one finite-dimensionality and Sturm injectivity, coefficient growth, and the needed
compactness machinery. Four local developments remain necessary:

1. a real-coefficient model for the normalized affine slice of modular forms;
2. a slightly generalized L-series positivity lemma, followed by the cusp-form sign-change lemma;
3. the finite-dimensional half-space/compactness argument;
4. the uniform Eisenstein-dominates-cusp estimate in finite coordinates.

No proof from Section 4 is included in Task 1.

## 2. Version decision

The first attempted pin was the stable pair Lean/mathlib `v4.32.1`. It compiled the q-expansion,
dimension, and growth probes, but it had no module
`Mathlib.NumberTheory.ModularForms.LFunction`. The initial project pin therefore used the exact
mathlib commit
`f0f4b227d8c5ac755232001fc0d94a440d399765`, whose declared Lean toolchain is
`leanprover/lean4:v4.34.0-rc1`. The local compiler identifies itself by commit
`3447a668783dbce1a8fdb97101dd067687b2b418`.

This is reproducible because both direct and transitive revisions are locked. The tradeoff is that
the project is pinned to a release candidate rather than the latest stable release. The pin should
not be advanced casually during the proof: several relevant APIs are recent.

## 3. Compiled positive findings

Every identifier below is imported and checked in `Section4/ApiProbe.lean`; the constructions at
the end of that file elaborate and compile.

### Fourier expansions and linearity

- `UpperHalfPlane.qExpansion` supplies the power series.
- `ModularForm.qExpansion_eq_zero_iff` gives q-expansion injectivity.
- `ModularForm.qExpansionAddHom` and `ModularForm.qExpansionRingHom` bundle additive and graded-ring
  structure.
- `CuspFormClass.qExpansion_coeff_zero` identifies the zero constant coefficient of a cusp form.
- There is no bundled fixed-weight complex-linear coefficient functional. The probe constructs
  `modularQCoeff k n : ModularForm 𝒮ℒ k →ₗ[ℂ] ℂ` and
  `cuspQCoeff k n : CuspForm 𝒮ℒ k →ₗ[ℂ] ℂ` directly from q-expansion additivity and scalar
  compatibility. This is routine and is not a blocker.

### Eisenstein series and the normalized affine slice

- `EisensteinSeries.E_qExpansion_coeff` gives, at positive `n`, exactly
  `-(2*k / bernoulli k) * sigma (k-1) n`.
- `EisensteinSeries.E_qExpansion_coeff_zero` gives constant coefficient `1`.
- `EisensteinSeries.E_ne_zero` proves the level-one Eisenstein series is nonzero.
- `ModularForm.toCuspForm` and `ModularForm.isCuspForm_iff_coeffZero_eq_zero` turn the difference
  between a normalized form and `E_k` into a cusp form once its constant coefficient is shown to
  vanish.

### Dimension and finite coordinates

- `ModularForm.dimension_level_one`, `ModularForm.rank_eq_one_add_rank_cuspForm`, and
  `ModularForm.sturm_bound_levelOne_nat` supply the expected level-one dimension and injectivity
  facts.
- `ModularForm.CuspForm.equivCuspFormSubmodule` is the actual fully qualified name of the
  cusp-form/submodule equivalence in this revision.
- `ModularForm 𝒮ℒ k` has a `FiniteDimensional ℂ` instance.
- `CuspForm 𝒮ℒ k` does **not** have that instance registered. The probe derives it with
  `FiniteDimensional.of_injective CuspForm.toModularFormₗ
  CuspForm.toModularFormₗ_injective`.
- Once this local complex finite-dimensionality proof is installed, restriction of scalars via
  `FiniteDimensional.trans ℝ ℂ _` compiles and produces real finite-dimensionality.

### Cusp coefficient growth

- `CuspFormClass.qExpansion_isBigO` gives, for each cusp form, coefficient growth
  `O(n^(k/2))` in mathlib's real-power notation. This is slightly weaker than the classical
  `d(n)n^((k-1)/2)` statement used in the paper but still has exponent strictly below the
  Eisenstein growth `n^(k-1)` for the weights in scope.
- `ModularFormClass.qExpansion_isBigO` gives the corresponding modular-form bound.
- `LSeries.abscissaOfAbsConv_le_of_isBigO_rpow` can translate a polynomial Big-O coefficient
  bound into a half-plane of absolute convergence.

The supplied cusp bound is pointwise in the form. The later proof needs a bound uniform on a
bounded finite-dimensional set. The clean route is to choose a finite real basis and combine the
finitely many basiswise Big-O estimates. No operator norm on the current cusp-form type is needed.

### L-functions and the sign-change input

- `ModularForm.weakFEPair`, `ModularForm.Λ`, and `ModularForm.L` define the completed and ordinary
  modular-form L-functions.
- `CuspForm.isStrongFEPair`, `CuspForm.differentiable_Λ`, and
  `CuspForm.differentiable_L` supply the functional equation package and prove that the ordinary
  L-function of a cusp form is entire.
- `CuspForm.hasSum_L` identifies the ordinary L-function with the Dirichlet series in a right
  half-plane. At level one, `Subgroup.strictWidthInfty_SL2Z` removes its cusp-width factor.
- A compiled probe proves `ModularForm.L hk f 0 = 0` by unfolding `ModularForm.L` and using
  `Complex.Gamma_zero` in the reciprocal Deligne Gamma factor.
- `LSeries.positive_of_differentiable_of_eqOn` contains almost exactly the analytic-continuation
  positivity argument needed for sign change.

The last theorem assumes `a 1 > 0`. A nonzero cusp form with nonnegative coefficients need not
have its first coefficient nonzero (for example, a cusp form may begin at `q^2`). Therefore the
existing theorem is not sufficient verbatim. Its proof is short and should be generalized locally
from `a 1 > 0` to `∃ n, 0 < a n`. Q-expansion injectivity supplies such an index under the
assumption that the cusp form is nonzero and all its real coefficients are nonnegative. Positivity
of the entire continuation at zero then contradicts the compiled equality `L(f,0)=0`.

This analytic argument is not a theorem proved in Section 4 of the paper itself: Section 4 invokes
the fact that a nonzero cusp form has a negative coefficient as a known input. In Lean, the recent
L-function API makes the analytic proof a plausible way to discharge that input internally.

### Compactness and finite half-spaces

- `isCompact_sphere` gives compactness of the unit sphere in a finite-dimensional Euclidean
  coordinate space.
- `IsCompact.elim_finite_subcover` extracts the finite set of coefficient directions used in the
  paper's open-cover argument.
- The audit did not find a mature polyhedron API matching the paper's terminology. In particular,
  the desired deliverable is most naturally stated directly as equality with an intersection over
  a `Finset`, rather than by introducing a separate `Polytope` structure.

The paper next uses the statement that every unbounded closed convex subset of `ℝ^ℓ` contains a
ray. That theorem was not located under a suitable existing API. It is unnecessary here: after
the finite subcover is chosen, continuity on the compact unit sphere supplies a uniform negative
margin for one of the finitely many homogeneous coefficient functionals. Scaling then gives an
explicit radius bound for the affine half-space intersection. This route is both shorter in Lean
and more reusable at higher level.

## 4. Missing or nonautomatic ingredients

### Real coefficients

Mathlib's modular forms and q-coefficients are complex-valued, while `0 ≤ a(n)` and real
half-spaces require real scalars. We should not silently order complex coefficients. Introduce a
real vector subspace consisting of cusp forms whose q-coefficients have zero imaginary part, and
use the real part as the coefficient functional. Q-expansion injectivity makes this definition
faithful. This abstraction should be separated from level-one facts so it can later be replaced by
the corresponding real form at prime level.

### Topology and norms on cusp forms

Temporary synthesis probes confirmed that `CuspForm 𝒮ℒ k` currently has neither a
`NormedAddCommGroup` nor a `NormedSpace` instance. Installing an arbitrary norm directly on that
type would create fragile global instance choices. Instead, carry out all convex geometry in a
chosen Euclidean coordinate space `Fin d → ℝ`, connected to the real cusp space by a linear
equivalence. This is the principal architectural adjustment forced by the API audit.

### Eisenstein positivity and lower growth

The exact coefficient formula and `ArithmeticFunction.sigma_pos` are present, but the audit found
no named theorem giving the required sign of `bernoulli k` for `k ≡ 0 (mod 4)`. It also found no
named lower bound `n^(k-1) ≤ sigma (k-1) n`, although that inequality is elementary because `n`
itself is a divisor of `n`. These should be isolated as small arithmetic lemmas. If proving the
Bernoulli sign directly becomes awkward, the level-one zeta/Bernoulli value formula is the natural
fallback; the choice should be settled in the arithmetic task, not mixed into the geometry.

### Uniformity

The pointwise cusp Big-O theorem does not itself say that one constant works for every form in a
bounded coordinate region. Choose a finite basis, obtain one asymptotic bound per basis vector,
take a finite maximum of the constants/thresholds, and combine with the coordinate radius. This
is precisely the finite-dimensional bridge needed for the paper's hyperplane-distance limit.

## 5. Originally recommended statement interfaces

The final user-facing well-definedness statement should say, schematically:

```lean
theorem exists_nonnegativity_bound_levelOne
    (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    ∃ N : ℕ, ∀ f : ModularForm 𝒮ℒ (k : ℤ),
      HasRealQExpansion f →
      realQCoeff f 0 = 1 →
      (∀ n, 1 ≤ n → n ≤ N → 0 ≤ realQCoeff f n) →
      ∀ n, 0 ≤ realQCoeff f n
```

The theorem corresponding most closely to Theorem 5 should retain the finite set:

```lean
theorem exists_finite_coefficient_test_levelOne
    (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    ∃ A : Finset ℕ,
      (∀ n ∈ A, 0 < n) ∧
      ∀ f : ModularForm 𝒮ℒ (k : ℤ),
        HasRealQExpansion f →
        realQCoeff f 0 = 1 →
        ((∀ n ∈ A, 0 ≤ realQCoeff f n) ↔
          ∀ n, 0 ≤ realQCoeff f n)
```

At Task 1 these names were provisional. The production resolution is stronger: reality and
normalization are bundled in `RealModularForm` and `NormalizedRealModularForm`, and the real
coefficient functions are `RealModularForm.coeff` and `NormalizedRealModularForm.coeff`.

Below these specialization theorems, the reusable geometric core should quantify over a
finite-dimensional real Euclidean space `V`, affine coefficient functionals
`e n + b n v`, and two analytic hypotheses:

1. every nonzero direction `v` has some `b n v < 0`;
2. on bounded subsets of `V`, `b n v` is eventually smaller in absolute value than the positive
   offset `e n`.

This cleanly separates compact convex geometry from modular forms. In a later weight-2,
prime-level project, only the construction of the normalized affine slice and the two analytic
hypotheses should change.

## 6. Original next-task boundary, now completed

Task 2 should define and prove the generic finite-dimensional half-space theorem only. It should
not yet mention modular forms. Its inputs should be stated so that the level-one and prospective
prime-level applications can share it. Only after that theorem compiles should the project add the
real cusp-form model and analytic sign-change input.

## 7. Historical Task 1 verification record

- `lake-manifest.json` records the exact direct and transitive revisions.
- `.\setup.ps1` has been run successfully against the existing local installation, including the
  pinned dependency update and compiled-cache check.
- `Section4/ApiProbe.lean` contains no `sorry`, `admit`, or added axiom.
- `.\lake.ps1 build` completes successfully: 3425 jobs, including `Section4.ApiProbe` and the
  library root `Section4`.

## 8. Final resolution

Every gap from the initial audit has a stable production implementation:

| Task 1 requirement | Final module and interface |
|---|---|
| Coefficientwise-real modular and cusp forms | `Section4.RealForms`: `RealModularForm`, `RealCuspForm`, and `NormalizedRealModularForm` |
| Real-linear coefficient functionals | `RealModularForm.coeffLinear`, `RealCuspForm.coeffLinear`, and `RealCuspForm.Coordinates.coeffContinuous` |
| Euclidean finite-dimensional coordinates without a global cusp-form norm | `RealCuspForm.Coordinates.Space`, `toForm`, and `ofForm` |
| Generalized L-series positivity | `Section4.LSeriesPositivity.positive_of_differentiable_of_eqOn_of_exists_pos` |
| Cusp-form sign change and directional obstruction | `RealCuspForm.exists_coeff_neg` and `RealCuspForm.Coordinates.detects_nonzero_direction` |
| Reusable compact half-space geometry | `Section4.FiniteHalfspace` |
| Normalized Eisenstein-cusp affine decomposition | `Section4.EisensteinDecomposition` |
| Bernoulli sign, positive Eisenstein coefficients, and lower growth | `Section4.EisensteinPositivity` |
| Uniform cusp control on bounded coordinate sets | `Section4.EisensteinDomination.eventuallyContainsClosedBalls` |
| Bounded finite convex-polytope theorem and finite coefficient test | `Section4.FiniteDetermination` |
| Least cutoff `A(k)`, first-negative maximum, and arbitrary-form theorem | `Section4.NonnegativityBound` |

The final invariant finite-test statement is

```lean
theorem FiniteDetermination.exists_finite_coefficient_test_levelOne
    (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    ∃ A : Finset ℕ,
      (∀ n ∈ A, 0 < n) ∧
      ∀ f : NormalizedRealModularForm (k : ℤ),
        ((∀ n ∈ A, 0 ≤ NormalizedRealModularForm.coeff f n) ↔
          ∀ n, 0 ≤ NormalizedRealModularForm.coeff f n)
```

The final least-cutoff interface is

```lean
noncomputable def NonnegativityBound.A (k : ℕ) : ℕ

theorem NonnegativityBound.isNonnegativityBound_iff_A_le
    (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (hNpos : 0 < N) :
    NonnegativityBound.IsNonnegativityBound k N ↔
      NonnegativityBound.A k ≤ N
```

For admissible `k ≥ 12`,
`NonnegativityBound.A_isGreatest_firstNegativeIndices_of_twelve_le` proves that this least
detecting endpoint is the paper's greatest finite first-negative index.

Two deliberate non-blockers remain:

1. no `Polytope` structure is introduced; the conclusion uses the paper's stated definition as a
   bounded convex finite intersection of closed affine half-spaces;
2. the real coordinate dimension is kept abstract instead of proving it equals the paper's
   explicit complex dimension. The proof and public invariant statements do not need that
   equality.

The production umbrella `Section4` does not import the Task 1 API probe or Task 2 spike. The
separate default target `Section4Audit` imports both, so a full build continues to detect upstream
API drift without exposing diagnostic declarations to production users.

The current compatibility pins, advanced together on 2026-09-24, are:

- Lean: `leanprover/lean4:v4.35.0-rc2`;
- compiler commit: `11acb17ec6b07a8f9e9173e6845197929540936b`;
- mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The final clean-build result is recorded in `FINAL_INTEGRATION.md`.
