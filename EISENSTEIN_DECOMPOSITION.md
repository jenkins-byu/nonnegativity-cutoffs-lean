# Task 6: normalized Eisenstein-cusp decomposition

## Result

Task 6 is complete. For a natural-number weight `k` satisfying

```lean
hkpos : 0 < k
hk4   : k % 4 = 0
```

the project now constructs the normalized level-one Eisenstein series as a
`RealModularForm (k : ℤ)`, proves that every normalized real modular form is uniquely the sum of
that Eisenstein series and a real cusp form, transports the cusp part to the Euclidean coordinate
space chosen in Task 4, and proves the affine coefficient identity needed for the later
half-space argument.

All of this is in `Section4/EisensteinDecomposition.lean`, in the namespace
`Section4.RealForms.EisensteinDecomposition`. No positivity or coefficient-growth estimate is
proved in this task.

## Admissible-weight arithmetic

The public hypotheses continue to match the intended level-one statement: `0 < k` and
`k % 4 = 0`. The small conversion layer in `AdmissibleWeight` proves exactly the forms required
by mathlib:

```lean
AdmissibleWeight.four_dvd : k % 4 = 0 → 4 ∣ k
AdmissibleWeight.four_le  : 0 < k → k % 4 = 0 → 4 ≤ k
AdmissibleWeight.three_le : 0 < k → k % 4 = 0 → 3 ≤ k
AdmissibleWeight.even     : k % 4 = 0 → Even k
```

Thus downstream definitions do not expose mathlib's lower-bound and parity hypotheses as extra
inputs.

## Real Eisenstein series

The definition

```lean
noncomputable def eisenstein
    (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    RealModularForm (k : ℤ)
```

bundles `ModularForm.E (AdmissibleWeight.three_le hkpos hk4)` together with a proof that every
q-expansion coefficient is real. That reality proof uses mathlib's full coefficient formula
`EisensteinSeries.E_qExpansion_coeff`; after splitting the constant and positive-index cases,
the imaginary parts vanish by simplification because the Bernoulli number, divisor sum, and
normalizing factors are real.

The normalization theorem is:

```lean
@[simp] theorem eisenstein_coeff_zero ... :
  RealModularForm.coeff (eisenstein k hkpos hk4) 0 = 1
```

The auxiliary theorem

```lean
RealModularForm.qExpansion_coeff_eq_coe
```

records that, for a real modular form, its complex q-expansion coefficient is the complex
embedding of the stored real coefficient. This is the bridge from the real normalization
condition to the complex zero-constant-term hypothesis expected by mathlib's cusp-form
constructor.

## Basis-free decomposition

For `f : NormalizedRealModularForm (k : ℤ)`, the definition

```lean
cuspDifference k hkpos hk4 f = f.1 - eisenstein k hkpos hk4
```

is first made in the real modular-form space. Its coefficients satisfy

```lean
cuspDifference_coeff ... f n :
  coeff (cuspDifference ... f) n =
    f.coeff n - coeff (eisenstein ...) n
```

and in particular `cuspDifference_coeff_zero` says that its constant coefficient is zero.
After translating that real equality back to the complex q-expansion, mathlib's
`ModularForm.toCuspForm` produces

```lean
noncomputable def cuspPart ...
    (f : NormalizedRealModularForm (k : ℤ)) : RealCuspForm (k : ℤ)
```

with no choice of basis. The principal decomposition theorem is:

```lean
theorem eq_eisenstein_add_cuspPart ... (f : NormalizedRealModularForm (k : ℤ)) :
  f.1 = eisenstein k hkpos hk4 +
    RealCuspForm.toRealModularForm (cuspPart k hkpos hk4 f)
```

The corresponding uniqueness statement is exported as:

```lean
theorem existsUnique_cuspPart ... (f : NormalizedRealModularForm (k : ℤ)) :
  ∃! g : RealCuspForm (k : ℤ),
    f.1 = eisenstein k hkpos hk4 + RealCuspForm.toRealModularForm g
```

Uniqueness uses only cancellation in the real modular-form space and injectivity of the inclusion
of real cusp forms. It is therefore independent of the coordinate choice.

## Coordinate transport and affine coefficients

The coordinate vector of the cusp part is

```lean
noncomputable def cuspCoordinates ... (f : NormalizedRealModularForm (k : ℤ)) :
  RealCuspForm.Coordinates.Space (k : ℤ)
```

and `coordinates_to_cuspPart` proves that applying Task 4's `toForm` equivalence recovers the
invariant cusp part. The project exports both the coordinate decomposition and its uniqueness:

```lean
eq_eisenstein_add_coordinates
existsUnique_coordinates
```

Finally, if

```lean
eisensteinCoeff k hkpos hk4 n =
  RealModularForm.coeff (eisenstein k hkpos hk4) n,
```

then the main Task 6 interface is:

```lean
theorem coeff_eq_eisenstein_add_coordinate ...
    (f : NormalizedRealModularForm (k : ℤ)) (n : ℕ) :
  NormalizedRealModularForm.coeff f n =
    eisensteinCoeff k hkpos hk4 n +
      RealCuspForm.Coordinates.coeffContinuous n
        (cuspCoordinates k hkpos hk4 f)
```

This has exactly the affine form required by the abstract finite-half-space theorem from Task 3:
the Eisenstein coefficient is the fixed term, and `coeffContinuous n` is the continuous linear
functional in the cusp coordinate vector.

## Dimension-formula assessment

Mathlib contains a complex rank formula for level-one modular forms in
`Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula`, including
`ModularForm.dimension_level_one` and the rank identity relating modular forms and cusp forms.
The Task 4 coordinate dimension, however, is

```lean
Module.finrank ℝ (RealCuspForm k),
```

where `RealCuspForm k` is the real-q-expansion fixed subspace. Identifying this real dimension
with the complex dimension of `CuspForm 𝒮ℒ k` requires a real-structure theorem: every complex
cusp form must be decomposed uniquely into real and imaginary parts that are themselves cusp
forms with real q-expansions. Mathlib's dimension formula does not directly provide that
identification, and the current project does not yet contain the required conjugation machinery.

Accordingly, Task 6 deliberately leaves the coordinate dimension abstract. This does not block
the decomposition, uniqueness, affine coefficient formula, sign-change obstruction, or the
finite-dimensional compactness argument. A closed formula for the dimension can be added later
as a separate lemma if explicit coordinate counts become useful.

## Verification boundary

The completed task proves:

1. the weight conversions needed to construct `E_k`;
2. coefficientwise reality and constant coefficient `1` for `E_k`;
3. existence and uniqueness of `f = E_k + g` with `g` a real cusp form;
4. existence and uniqueness of the corresponding cusp coordinate vector;
5. the affine coefficient identity in continuous-linear coordinate form.

It does not prove that positive-index Eisenstein coefficients are positive, establish any lower
growth bound for them, compare them with cusp coefficients, or apply the generic finite-half-space
theorem. Those are intentionally left for the subsequent tasks.
