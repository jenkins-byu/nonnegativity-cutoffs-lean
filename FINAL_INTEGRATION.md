# Task 11: final integration and verification

Date completed: 2026-08-24

## Scope and source version

This report describes the completed qualitative Lean formalization of Section 4, Theorem 5 of
Paul Jenkins and Jeremy Rouse,
[*Modular Forms with Only Nonnegative Coefficients*](https://doi.org/10.1007/s40993-026-00744-z),
*Research in Number Theory* **12**, article 56 (2026). The development was originally checked
against [arXiv:2507.17949v3](https://arxiv.org/abs/2507.17949v3), dated 31 March 2026; the relevant
section is substantively unchanged in the published version. Section 4 proves the
well-definedness of `A(k)`.

The formalization covers the qualitative level-one argument. It does not cover the numerical
computations in Section 3, the explicit lower bound in Section 5, or the explicit upper and
coefficient bounds in Section 6.

## Production and audit surfaces

The production umbrella is `Section4.lean`. It imports only the stable mathematical modules:

```text
FiniteHalfspace
LSeriesPositivity
RealForms
RealCuspSignChange
EisensteinDecomposition
EisensteinPositivity
EisensteinDomination
FiniteDetermination
NonnegativityBound
```

The Task 1 API probe and Task 2 feasibility spike remain useful regression tests, but are not part
of the production import surface. They are imported by the separate umbrella
`Section4Audit.lean`. The package declares both `Section4` and `Section4Audit` as default targets,
so `.\lake.ps1 build` still verifies every source file.

This resolves the remaining provisional boundary: production code no longer depends on the raw
probe coefficient maps or the spike's explicit `Complex.re`/`Complex.im` hypotheses. Those roles
are filled by `RealModularForm.coeffLinear`, `RealCuspForm.coeffLinear`, and
`RealCuspForm.exists_coeff_neg`.

## Production dependency graph

```text
FiniteHalfspace -------------------------------+
                                                |
RealForms -> EisensteinDecomposition            |
               -> EisensteinPositivity          |
                    -> EisensteinDomination <---+
                              |
LSeriesPositivity -> RealCuspSignChange         |
                              |                 |
                              +-> FiniteDetermination
                                      |
                                      +-> NonnegativityBound
```

`NonnegativityBound` also imports mathlib's level-one graded-ring results to prove that the
discriminant has real q-expansion and to construct a nonzero real cusp direction in every
admissible weight at least twelve.

## Correspondence with Section 4

The following table maps the paper's objects and assertions to the stable Lean interface.

| Paper item | Lean declaration | Status and interpretation |
|---|---|---|
| The normalized affine space of forms `1 + O(q)` | `NormalizedRealModularForm`; `FiniteDetermination.normalizedFormsEquivCoordinates` | The normalization and coefficientwise reality are enforced by bundled types. The affine slice is equivalent to the full real cusp-coordinate space. |
| Canonical coordinates `(a(1), ..., a(ℓ)) ∈ ℝ^ℓ` | `RealCuspForm.Coordinates.Space`; `EisensteinDecomposition.cuspCoordinates` | Lean uses a noncomputably chosen Euclidean basis of the real cusp space. The public real-form definitions remain basis-free. |
| The coefficient half-space `S_n` | `FiniteDetermination.coefficientHalfspace` | Its defining inequality is the affine coefficient functional `a_E(n) + b_n(v) ≥ 0`. |
| The feasible set `S = ⋂_n S_n` | `FiniteDetermination.nonnegativeCoordinates` | `cuspCoordinates_mem_nonnegativeCoordinates_iff` identifies membership exactly with coefficientwise nonnegativity of the corresponding normalized form. |
| `S` is closed | `FiniteDetermination.isClosed_nonnegativeCoordinates` | Proved from closed affine half-spaces. |
| `S` is convex | `FiniteDetermination.convex_nonnegativeCoordinates` | Proved abstractly for intersections of affine half-spaces. |
| A nonzero cusp direction has a negative coefficient, so the homogeneous intersection is `{0}` | `RealCuspForm.exists_coeff_neg`; `RealCuspForm.Coordinates.detects_nonzero_direction` | The paper cites this as well known. Lean proves it internally through the analytic properties of the cusp-form L-function. |
| A finite set of homogeneous directions bounds the affine intersection | `FiniteHalfspace.exists_bounded_finiteIntersection`; `FiniteDetermination.isBounded_nonnegativeCoordinates` | The compact unit-sphere argument is formalized once in the reusable geometric module. |
| The Eisenstein part eventually dominates every cusp direction on the bounded region | `EisensteinDomination.eventuallyContainsClosedBalls` | Finite-coordinate uniformity replaces the paper's hyperplane-distance formulation. |
| **Theorem 5:** `S` is a bounded finite convex polytope | `FiniteDetermination.exists_bounded_finite_convex_polytope` | The Lean conclusion records boundedness, compactness, convexity, and equality with a finite intersection of closed affine half-spaces. |
| The finite set consists of positive indices | The positivity clause in `exists_bounded_finite_convex_polytope` and `exists_finite_coefficient_test_levelOne` | Index zero is removed because the normalized constant-coefficient inequality is automatic. |
| Nonnegativity is detected by a finite coefficient set | `FiniteDetermination.exists_finite_coefficient_test_levelOne` | This is the invariant form of the direct corollary following Theorem 5. |
| Some initial segment detects nonnegativity | `FiniteDetermination.exists_initial_coefficient_test_levelOne`; `exists_nonnegativity_bound_levelOne` | Taking the maximum of the finite positive test set produces an inclusive endpoint. |
| `A(k)` is well-defined | `NonnegativityBound.A`; `A_spec`; `isNonnegativityBound_iff_A_le` | Lean defines the least positive successful endpoint and proves its complete order-theoretic specification. |
| Paper definition `A(k) = max {N(f) : N(f) < ∞}` | `FirstNegativeAt`; `firstNegativeIndices`; `A_isGreatest_firstNegativeIndices_of_twelve_le` | For every admissible `k ≥ 12`, Lean proves that the least detecting endpoint is exactly the greatest first-negative index. |
| Empty low-weight cases | `A_four`; `A_eight` | Under the selected least-positive convention, both values are `1`. |
| Reduction from arbitrary forms to normalized forms | `realModularForm_nonnegative_of_nonnegative_up_to_A`; `firstNegativeAt_le_A` | Lean explicitly treats negative, zero, and positive constant coefficients. |

Here "bounded finite convex polytope" has the paper's stated meaning: a bounded convex set equal
to an intersection of finitely many closed affine half-spaces. No separate mathlib `Polytope`
structure is introduced.

## Differences between the paper and Lean proof

### 1. Real coefficients are explicit

Mathlib's modular forms are complex-valued. The paper's inequalities tacitly restrict attention
to forms with real Fourier coefficients. Lean defines coefficientwise-real modular and cusp-form
submodules and takes real parts only after proving that all imaginary parts vanish. It never uses
an order on arbitrary complex coefficients.

### 2. Coordinates are invariant rather than canonical

The paper identifies a normalized form with its first `ℓ` Fourier coefficients. Lean uses an
arbitrary finite real basis of `RealCuspForm` and proves a coordinate equivalence with the entire
normalized affine slice. This avoids formalizing the equality between the real dimension and the
paper's explicit complex dimension `ℓ = ⌊k/12⌋`; that equality is unnecessary for Theorem 5.

### 3. The sign-change input is proved internally

Section 4 invokes the fact that every nonzero cusp form has a negative coefficient. Lean proves
this for coefficientwise-real level-one cusp forms. If all coefficients were nonnegative, a
nonzero coefficient would make the associated Dirichlet series positive; analytic continuation
would then make the ordinary cusp-form L-function positive at zero, contradicting its vanishing
there through the reciprocal Gamma factor.

### 4. Boundedness avoids an unneeded recession-ray theorem

The paper says that an unbounded closed convex set contains a ray. The reusable Lean argument
instead takes a finite subcover of the compact unit sphere, obtains a uniform negative margin in
every direction, and scales that margin to an explicit radius bound. The conclusion is the same,
but the Lean proof needs less external convex-analysis infrastructure.

### 5. Finite reduction is phrased as uniform tail containment

The paper shows that the distance from the origin to the boundary of `S_n` tends to infinity.
Lean proves the equivalent operational statement needed on a bounded coordinate ball: eventually,
every late half-space contains that ball. The cusp coefficient input is mathlib's qualitative
`O(n^(k/2))` estimate, rather than the sharper `d(n)n^((k-1)/2)` estimate in the paper. Since
`k/2 < k-1` for the admissible weights, the weaker exponent still suffices against the
Eisenstein lower growth `n^(k-1)`.

### 6. The formal definition of `A(k)` starts with a minimum

The paper initially defines `A(k)` as a maximum of finite first-negative indices and uses Theorem
5 to prove that the set is bounded. Lean first defines `A(k)` as the least positive detecting
endpoint supplied by finite determination. Minimality then constructs an extremizing normalized
form, and Lean proves that this minimum is the paper's maximum in every admissible weight at least
twelve. This direction handles well-definedness before requiring nonemptiness of the
first-negative family.

### 7. The zero constant coefficient is handled constructively

For an arbitrary real form with zero constant coefficient, direct normalization is impossible.
If such a form were nonnegative through `A(k)` but negative later, Lean adds a suitable positive
multiple of it to `E_k`. The result is normalized, remains nonnegative through `A(k)`, and has a
later coefficient equal to `-1`, contradicting the normalized cutoff theorem.

## Deliberate scope boundaries

- The development is qualitative and noncomputable. It proves that a finite cutoff exists but
  does not calculate the values in the paper's tables, except for `A(4)` and `A(8)` under the
  empty-family convention.
- It concerns coefficientwise-real level-one modular forms. It does not order genuinely complex
  coefficients.
- It does not formalize the sharper coefficient estimates and explicit constants needed for
  Theorems 1-4 and 9.
- It does not prove the optional equality between the real cusp-space dimension and the paper's
  explicit `ℓ`; no theorem in this project depends on that equality.

## Reproducibility

The project is pinned by three checked-in files:

- `lean-toolchain`: `leanprover/lean4:v4.35.0-rc2`;
- `lakefile.toml`: mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`;
- `lake-manifest.json`: exact revisions of every transitive package.

On Windows PowerShell, initial setup and ordinary verification are:

```powershell
.\setup.ps1
.\lake.ps1 build
```

A clean verification of all project sources is:

```powershell
.\lake.ps1 clean
.\lake.ps1 build
```

The two import surfaces may be verified separately with:

```powershell
.\lake.ps1 build Section4
.\lake.ps1 build Section4Audit
```

## Final verification record

The final verification checks:

- a clean build of both default targets;
- an independent production-umbrella build;
- an independent audit/regression-umbrella build;
- absence of `sorry`, `admit`, `axiom`, and `#check` from production sources;
- absence of added axiom declarations from the entire project.

All checks were run on 24 August 2026 with
`Lean 4.34.0-rc1` (`x86_64-w64-windows-gnu`, commit
`3447a668783dbce1a8fdb97101dd067687b2b418`).

1. `.\lake.ps1 clean`, followed by `.\lake.ps1 build`, completed successfully from an empty
   build directory: **3,445 jobs**. This built both default targets, including the production
   modules and the two diagnostic/regression modules.
2. `.\lake.ps1 build Section4` completed successfully: **3,434 jobs**.
3. `.\lake.ps1 build Section4Audit` completed successfully: **3,427 jobs**. The displayed
   `info:` lines are the intentional output of the API probe's `#check` commands; they are not
   compiler warnings.
4. A source scan of every project Lean file found no `sorry`, `admit`, or project `axiom`
   declaration.
5. A separate scan of the production umbrella and its nine modules found no `#check` command and
   no import or reference to `ApiProbe` or `SignChangeSpike`.
6. Lean's `#print axioms` audit of the sign-change theorem, Theorem 5 analogue, `A_spec`, and the
   final greatest-first-negative-index theorem reported only `propext`, `Classical.choice`, and
   `Quot.sound`. In particular, it reported neither `sorryAx` nor any project-specific axiom.

The build emitted no compiler warnings or errors. Thus the production theorem chain and the
separate API regression surface both verify under the checked-in pins.

## Lean 4.35 compatibility verification

On 24 September 2026, the project was advanced to Lean `v4.35.0-rc2` (compiler commit
`11acb17ec6b07a8f9e9173e6845197929540936b`) and the matching Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. No Lean source changes were required.

After removing all compiled outputs, the full default build completed successfully with 3,507
jobs. A fresh source scan found exactly the one intentional `sorry` in `Challenge.lean` and no
`admit`, `native_decide`, `Lean.ofReduceBool`, project `axiom`, or `unsafe` declaration. A fresh
`#print axioms` audit of
`NonnegativeModularForms.exists_optimal_nonnegativity_cutoff` again reported exactly `propext`,
`Classical.choice`, and `Quot.sound`.
