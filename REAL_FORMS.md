# Task 4: real modular forms and cusp-form coordinates

Date: 2026-08-18

## Result

The invariant real-q-expansion layer and the level-one real modular-form spaces are fully
formalized. The implementation supplies the finite-dimensional Euclidean coordinate interface
needed by the generic half-space theorem while keeping every public definition independent of a
basis.

No sign-change theorem, Eisenstein decomposition, or coefficient-growth estimate was moved into
this task.

## Generic definitions

For any bundled function with values in `ℂ`, the predicate

```lean
HasRealQExpansionAt h f
```

means

```lean
∀ n : ℕ, ((UpperHalfPlane.qExpansion h f).coeff n).im = 0.
```

The real part of a coefficient is exposed as

```lean
realQCoeffAt h f n : ℝ.
```

For a subgroup `Γ`, integral weight `k`, positive expansion width `h`, and a proof that `h` is a
strict period, the file defines

```lean
realModularFormSubmodule Γ k h hh hΓ : Submodule ℝ (ModularForm Γ k)
realCuspFormSubmodule Γ k h hh hΓ : Submodule ℝ (CuspForm Γ k).
```

Their construction proves closure under zero, addition, and real scalar multiplication from
mathlib's q-expansion identities. Thus the coefficientwise-real construction itself is not tied
to level one.

## Level-one spaces

Specializing to width `1` gives the basis-free types

```lean
RealModularForm k
RealCuspForm k.
```

Both are submodule subtypes of the existing complex spaces. Their coefficient functions are

```lean
RealModularForm.coeff f n : ℝ
RealCuspForm.coeff f n : ℝ,
```

and evaluation at each fixed `n` is bundled as a real-linear map:

```lean
RealModularForm.coeffLinear n : RealModularForm k →ₗ[ℝ] ℝ
RealCuspForm.coeffLinear n : RealCuspForm k →ₗ[ℝ] ℝ.
```

The inclusion of cusp forms into modular forms restricts to a real-linear injection

```lean
RealCuspForm.toRealModularForm : RealCuspForm k →ₗ[ℝ] RealModularForm k.
```

It preserves every real q-expansion coefficient.

## Injectivity

The file proves that real coefficients determine the form:

```lean
RealModularForm.ext
RealModularForm.coeff_injective
RealCuspForm.ext
RealCuspForm.coeff_injective.
```

For modular forms, the proof reconstructs equality of the complex q-expansions from equality of
real parts and the stored vanishing of imaginary parts, then applies
`ModularForm.qExpansion_eq_zero_iff`. The cusp-form result uses the injective inclusion into
modular forms.

It also records

```lean
RealCuspForm.coeff_zero f : RealCuspForm.coeff f 0 = 0.
```

This will let Task 5 strengthen the negative-coefficient witness to a positive index without an
extra public hypothesis.

## Normalized forms

The normalized affine slice is represented without choosing coordinates:

```lean
NormalizedRealModularForm k :=
  {f : RealModularForm k // RealModularForm.coeff f 0 = 1}.
```

Its coefficient function and constant-coefficient theorem are

```lean
NormalizedRealModularForm.coeff f n
NormalizedRealModularForm.coeff_zero f.
```

This is a subtype rather than a submodule because the condition `a(0) = 1` is affine, not linear.

## Finite-dimensionality and coordinates

The file registers

```lean
FiniteDimensional ℝ (RealModularForm k)
FiniteDimensional ℝ (RealCuspForm k).
```

For cusp forms, the proof first derives the missing complex finite-dimensionality instance using
the injection into modular forms, restricts scalars from `ℂ` to `ℝ`, and then uses finite
dimensionality of submodules.

The internal coordinate namespace defines

```lean
RealCuspForm.Coordinates.dimension k
RealCuspForm.Coordinates.Space k
```

with

```lean
Space k = Fin (Module.finrank ℝ (RealCuspForm k)) → ℝ.
```

A noncomputably chosen finite basis gives inverse real-linear equivalences

```lean
RealCuspForm.Coordinates.toForm k : Space k ≃ₗ[ℝ] RealCuspForm k
RealCuspForm.Coordinates.ofForm k : RealCuspForm k ≃ₗ[ℝ] Space k.
```

The basis itself is not exported and does not occur in the definition of a real or normalized
form. The coordinate coefficient functionals are bundled in the form required by Task 3:

```lean
RealCuspForm.Coordinates.coeffContinuous n : Space k →L[ℝ] ℝ.
```

Their evaluation theorem identifies them with the invariant cusp-form coefficients after applying
`toForm`.

## Scope and downstream use

Task 5 can now restate the compiled sign-change spike directly for `RealCuspForm`, with no raw
`Complex.im` hypothesis. Task 6 can construct the normalized Eisenstein-cusp decomposition in the
public basis-free types and then transport its cusp component through `ofForm`. Tasks 8 and 9 can
use `coeffContinuous` as the linear part of the affine half-spaces formalized in Task 3.

The construction is classical and noncomputable, consistently with the approved objective of
proving existence rather than calculating `A(k)`.

## Verification

- Source: `Section4/RealForms.lean`.
- The library root `Section4.lean` imports the source.
- The source compiles without warnings.
- It contains no `sorry`, `admit`, or added axiom.
- Verification command: `.\lake.ps1 build`.
