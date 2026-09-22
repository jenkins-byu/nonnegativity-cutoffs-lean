# Nonnegativity cutoffs for level-one modular forms in Lean

This project formalizes the qualitative argument in Section 4 of Paul Jenkins and Jeremy Rouse,
[*Modular Forms with Only Nonnegative Coefficients*](https://doi.org/10.1007/s40993-026-00744-z),
*Research in Number Theory* **12**, article 56 (2026). The source article is open access. The
development was originally checked against arXiv:2507.17949v3; the relevant section is
substantively unchanged in the published version.

## Main result

For every weight `k ≥ 12` divisible by four, the formalization proves that there is a positive
inclusive index `A` with both of the following properties:

1. every real level-one modular form whose Fourier coefficients through `A`, including the
   constant coefficient, are nonnegative has all Fourier coefficients nonnegative; and
2. `A` is attained as, and bounds, the first negative coefficient index of every such form which
   has a negative coefficient.

Thus `A` is the greatest possible first negative index and gives a finite coefficient test for
global nonnegativity. The full development also proves the bounded finite convex-polytope and
finite-determination statements for the normalized affine slice used in Section 4.

The small Palomar review surface is [`Challenge.lean`](Challenge.lean). Its proved counterpart is
[`Solution.lean`](Solution.lean), and [`comparator.json`](comparator.json) selects their single
headline declaration. [`PALOMAR_SUBMISSION.md`](PALOMAR_SUBMISSION.md) records the intended
correspondence, scope, automation disclosure, and completed author review.

## Completion status

The qualitative level-one formalization of Section 4 is complete. It covers Theorem 5, finite
coefficient determination, well-definedness and the least-cutoff specification of `A(k)`, the
paper-style maximum characterization in every admissible weight `k ≥ 12`, and the empty cases
in weights four and eight. It does not formalize the explicit numerical estimates from Sections
3, 5, or 6 of the paper.

The production import is:

```lean
import Section4
```

The diagnostic API probes and the original sign-change spike are kept behind a separate import:

```lean
import Section4Audit
```

## Exact pin

- Lean toolchain: `leanprover/lean4:v4.34.0-rc1`
- Lean compiler commit reported locally: `3447a668783dbce1a8fdb97101dd067687b2b418`
- mathlib commit: `f0f4b227d8c5ac755232001fc0d94a440d399765`
- All transitive package revisions are recorded in `lake-manifest.json`.

The exact mathlib commit is intentional. The tested stable release, mathlib `v4.32.1`, did not
contain `Mathlib.NumberTheory.ModularForms.LFunction`; this pinned post-release revision does.

## Build on Windows

From this directory in PowerShell:

```powershell
.\setup.ps1
.\lake.ps1 build
```

`setup.ps1` installs Elan under `.elan/`, obtains the pinned toolchain, resolves the locked Lake
dependencies, and downloads mathlib's compiled cache. These downloaded directories are ignored.
`lake.ps1` uses only the project-local installation. Its Git ownership override is process-local
and exists to make builds work in host/sandbox combinations that assign different filesystem
owners to downloaded Lake packages.

For a clean verification after setup:

```powershell
.\lake.ps1 clean
.\lake.ps1 build
```

The default build compiles the production library, the separate audit/regression target, and the
Palomar Challenge and Solution modules. They can also be checked independently:

```powershell
.\lake.ps1 build Section4
.\lake.ps1 build Section4Audit
.\lake.ps1 build Challenge
.\lake.ps1 build Solution
```

`Challenge.lean` deliberately contains one `sorry`, as required for Palomar's advertised
statement module. `Solution.lean` and the production development contain no `sorry`.

## Palomar preparation files

- `Challenge.lean`: the short Mathlib-only statement a mathematical reader should audit.
- `Solution.lean`: the identically typed theorem proved from the production development.
- `comparator.json`: the declaration and permitted-axiom configuration.
- `formalization.yaml`: authorship, source, scope, fidelity, automation, and review metadata.
- `PALOMAR_SUBMISSION.md`: local preparation status and semantic review checklist.
- `LICENSE`: Apache License 2.0.
- `CITATION.cff`: citation metadata for the formalization and published source.

## Production files

- `Section4/FiniteHalfspace.lean`: the generic finite-dimensional compactness argument, including
  finite-set and initial-segment reductions and compactness/convexity corollaries.
- `Section4/RealForms.lean`: generic coefficientwise-real q-expansion submodules, their level-one
  specializations, normalized real forms, and internal cusp-form coordinates.
- `Section4/LSeriesPositivity.lean`: the reusable generalization of L-series positivity from a
  positive first coefficient to a positive coefficient at an arbitrary nonzero index.
- `Section4/RealCuspSignChange.lean`: the production sign-change and zero-detection theorems for
  real level-one cusp forms, including the coordinate directional-obstruction interface.
- `Section4/EisensteinDecomposition.lean`: admissible-weight arithmetic, the normalized
  Eisenstein series as a real modular form, the unique Eisenstein-cusp decomposition, and its
  coordinatewise affine coefficient identity.
- `Section4/EisensteinPositivity.lean`: the Bernoulli-number sign in weights divisible by four,
  positivity of nonconstant Eisenstein coefficients, and their polynomial lower-growth bound.
- `Section4/EisensteinDomination.lean`: pointwise cusp-coefficient growth, its finite-coordinate
  uniformization, and the eventual closed-ball containment theorem needed for finite reduction.
- `Section4/FiniteDetermination.lean`: the normalized affine-slice coordinate equivalence,
  bounded finite convex-polytope theorem, positive-index finite test, and initial cutoff theorem.
- `Section4/NonnegativityBound.lean`: the least positive cutoff `A(k)`, first-negative-index
  characterizations, the arbitrary-real-form theorem, nontrivial-range attainment, and the
  weight-four and weight-eight values.
- `Section4.lean`: the production umbrella.

## Audit and regression files

- `Section4/ApiProbe.lean`: compiled checks and small constructions for the external mathlib APIs
  on which the architecture depends.
- `Section4/SignChangeSpike.lean`: the original raw analytic feasibility proof, retained as a
  regression check; the production theorem is in `Section4/RealCuspSignChange.lean`.
- `Section4Audit.lean`: the separate audit/regression umbrella and second default build target.

## Reports

- `API_AUDIT.md`: the original Task 1 findings together with the Task 11 resolution of every
  identified gap and the final production interfaces.
- `SIGN_CHANGE_SPIKE.md`: the precise Task 2 proof route and feasibility result.
- `FINITE_HALFSPACE.md`: the precise Task 3 theorem interfaces, proof structure, and downstream
  obligations.
- `REAL_FORMS.md`: the precise Task 4 definitions, exported results, and coordinate interface.
- `REAL_CUSP_SIGN_CHANGE.md`: the precise Task 5 public statements and analytic proof route.
- `EISENSTEIN_DECOMPOSITION.md`: the precise Task 6 definitions, theorem interfaces, proof
  structure, and the dimension-formula assessment.
- `EISENSTEIN_POSITIVITY.md`: the precise Task 7 arithmetic inputs, exported growth interfaces,
  proof structure, and downstream contract for the uniform cusp estimate.
- `EISENSTEIN_DOMINATION.md`: the precise Task 8 uniform-growth construction, exported tail
  theorem, and contract for applying the abstract finite-half-space theorem in Task 9.
- `FINITE_DETERMINATION.md`: the precise Task 9 specialization, its final Section 4 theorem
  interfaces, indexing conventions, and the input used to define `A(k)` in Task 10.
- `NONNEGATIVITY_BOUND.md`: the precise Task 10 definition, public theorem interfaces,
  proof structure, endpoint conventions, and noncomputability boundary.
- `FINAL_INTEGRATION.md`: the Task 11 production dependency graph, theorem-by-theorem
  correspondence with Section 4, proof differences, scope boundary, and final verification record.

The project verification command is `.\lake.ps1 build`.
