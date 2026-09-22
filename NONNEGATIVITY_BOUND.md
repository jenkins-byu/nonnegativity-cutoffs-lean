# Task 10: the least nonnegativity bound `A(k)`

Date completed: 2026-08-21

## Result

Task 10 is complete. The production implementation is
`Section4/NonnegativityBound.lean`, in the namespace
`Section4.RealForms.NonnegativityBound`.

For every positive natural-number weight divisible by four, the module defines `A(k)` as the
least positive inclusive endpoint for which nonnegativity of the coefficients with indices
`1, ..., A(k)` forces global coefficientwise nonnegativity on the normalized real affine slice.
It proves the defining specification and minimality, relates `A(k)` to first negative
coefficients, extends the detection theorem to arbitrary real modular forms, proves the maximum
characterization unconditionally for admissible `k >= 12`, and proves the selected empty-family
values `A(4) = A(8) = 1`.

## Definition and endpoint convention

The detection predicate is

```lean
def IsNonnegativityBound (k N : ℕ) : Prop :=
  ∀ f : NormalizedRealModularForm (k : ℤ),
    (∀ n, 1 ≤ n → n ≤ N → 0 ≤ NormalizedRealModularForm.coeff f n) →
      ∀ n, 0 ≤ NormalizedRealModularForm.coeff f n
```

The endpoint is inclusive and required to be positive. The definition is an ordinary function
of the weight:

```lean
noncomputable def A (k : ℕ) : ℕ
```

When `0 < k` and `k % 4 = 0`, it uses `Nat.find` to select the least positive successful cutoff
from Task 9's existence theorem. Outside that domain it is set to `1`. This total fallback keeps
the public term simple without asserting modular-form mathematics outside the intended domain.
The project proves positivity for every input:

```lean
theorem A_pos (k : ℕ) : 0 < A k
```

## Detection, minimality, and monotonicity

The defining specification is exported as

```lean
theorem A_spec (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
  0 < A k ∧ IsNonnegativityBound k (A k)
```

The two main directions are also available separately:

```lean
theorem A_detects_nonnegativity ... : IsNonnegativityBound k (A k)

theorem A_le_of_pos_of_isNonnegativityBound ...
    (hNpos : 0 < N) (hN : IsNonnegativityBound k N) : A k ≤ N
```

The predicate is monotone in the endpoint:

```lean
theorem isNonnegativityBound_mono (hNM : N ≤ M)
    (hN : IsNonnegativityBound k N) : IsNonnegativityBound k M
```

Combining monotonicity and minimality gives the exact characterization of every positive
endpoint:

```lean
theorem isNonnegativityBound_iff_A_le ... (hNpos : 0 < N) :
  IsNonnegativityBound k N ↔ A k ≤ N
```

Thus `A(k)` is not merely a chosen finite bound; Lean verifies that it is the least positive
bound under the agreed convention.

## First negative coefficients

For an arbitrary real modular form, the module defines

```lean
def FirstNegativeAt (f : RealModularForm k) (n : ℕ) : Prop :=
  RealModularForm.coeff f n < 0 ∧
    ∀ m, m < n → 0 ≤ RealModularForm.coeff f m
```

and the corresponding predicate `NormalizedFirstNegativeAt` for normalized forms. Existence from
any negative coefficient and uniqueness of the first negative index are proved. A normalized
first negative index is positive, and every such index satisfies

```lean
theorem normalized_firstNegativeAt_le_A ... : n ≤ A k
```

Minimality of `A(k)` supplies an extremizer whenever the normalized counterexample family is
nonempty:

```lean
theorem exists_normalized_firstNegativeAt_A ...
    (hnontrivial : HasNegativeNormalizedForm k) :
  ∃ f, NormalizedFirstNegativeAt f (A k)
```

Consequently `A(k)` is the greatest member of `normalizedFirstNegativeIndices k` under the same
hypothesis.

## Why the nontrivial range really is `k >= 12`

The implementation discharges the preceding nonemptiness hypothesis for every admissible
`k >= 12`, rather than leaving it as an external assumption.

First, it proves that the modular discriminant has coefficientwise-real q-expansion. The proof
uses mathlib's identity

```text
Δ = (E₄³ - E₆²) / 1728
```

and closure of coefficientwise-real q-expansions under multiplication, subtraction, real scalar
multiplication, and weight casts. For `k > 12`, it then constructs the nonzero real cusp form
`Δ E_(k-12)`; nonzeroness uses mathlib's no-zero-divisors theorem for products of modular
forms. Weight twelve uses `Δ` itself.

Task 5's analytic sign-change theorem gives a negative coefficient `b_n` of that cusp form.
Writing `e_n` for the corresponding Eisenstein coefficient, the normalized form

```text
E_k + ((e_n + 1) / (-b_n)) g
```

has coefficient `-1` at `n`. This proves

```lean
theorem hasNegativeNormalizedForm_of_twelve_le ... (hk12 : 12 ≤ k) :
  HasNegativeNormalizedForm k
```

and yields unconditional nontrivial-range forms of the main conclusions:

```lean
theorem exists_normalized_firstNegativeAt_A_of_twelve_le ...
theorem A_isGreatest_normalizedFirstNegativeIndices_of_twelve_le ...
theorem A_isGreatest_firstNegativeIndices_of_twelve_le ...
```

The last theorem states the paper-style maximum characterization using first negative indices of
all real level-one modular forms, not only normalized ones.

## Arbitrary real modular forms

The normalized cutoff also controls arbitrary coefficientwise-real modular forms, provided the
tested segment includes the constant coefficient:

```lean
theorem realModularForm_nonnegative_of_nonnegative_up_to_A ...
    (f : RealModularForm (k : ℤ))
    (hinitial : ∀ n, n ≤ A k → 0 ≤ RealModularForm.coeff f n) :
    ∀ n, 0 ≤ RealModularForm.coeff f n
```

The proof splits according to the constant coefficient `c`:

1. If `c < 0`, the hypothesis at index zero is already contradictory.
2. If `c > 0`, multiplication by `c⁻¹` normalizes the form and reduces the result to
   `A_detects_nonnegativity`.
3. If `c = 0` and a later coefficient `a_n` were negative, choose
   `t = (e_n + 1) / (-a_n) > 0`. Then `E_k + t f` is normalized, remains nonnegative through
   `A(k)`, and has coefficient `-1` at `n`, contradicting normalized detection.

It follows that every first negative index of an arbitrary real modular form is at most `A(k)`.
Together with the normalized extremizer in weights at least twelve, this proves the maximum
characterization for the arbitrary-form set `firstNegativeIndices k`.

## Empty normalized families

Below weight twelve, mathlib's level-one dimension formula makes the cusp space zero. Task 6's
Eisenstein-cusp decomposition then shows that every normalized form is the normalized Eisenstein
series, whose coefficients are nonnegative by Task 7. Therefore there are no normalized forms
with a negative coefficient in weights four and eight.

The chosen least-positive-endpoint convention consequently gives

```lean
theorem A_four : A 4 = 1
theorem A_eight : A 8 = 1
```

This convention avoids taking the maximum of an empty set while retaining the paper's intended
finite-test interpretation.

## Noncomputability and generalization boundary

`A(k)` is noncomputable because Task 9 obtains a successful cutoff through compactness and
asymptotic estimates. The module proves existence and the exact order-theoretic characterization;
it does not calculate numerical values beyond the empty-family cases `4` and `8`.

The reusable concepts are deliberately separated:

- `IsNonnegativityBound` records the normalized cutoff property;
- `FirstNegativeAt` is independent of normalization and of level-one-specific coordinates;
- the arbitrary-form argument needs only a normalized positive Eisenstein direction and the
  normalized cutoff theorem;
- the proof that the nontrivial range begins at twelve is level-one-specific, through `Δ` and
  the level-one dimension formula.

For a later weight-two prime-level project, the least-cutoff and first-negative order theory can
be reused. The level-dependent work remains the construction of the normalized affine slice,
its finite-determination theorem, and an appropriate nonempty real cusp direction.

## Verification

- Production source: `Section4/NonnegativityBound.lean`.
- The library root `Section4.lean` imports the production source.
- Verification command: `.\lake.ps1 build`.
