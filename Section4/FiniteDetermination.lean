import Section4.EisensteinDomination
import Section4.RealCuspSignChange

/-!
# Finite determination of coefficientwise nonnegativity

This file specializes the abstract finite-half-space theorem to normalized real level-one
modular forms.  It is the final assembly step in the formalization of Section 4: the sign-change
theorem supplies boundedness in every cusp direction, and uniform Eisenstein domination supplies
the eventual-tail hypothesis.
-/

open Metric Set
open scoped MatrixGroups UpperHalfPlane Topology

namespace Section4.RealForms

namespace FiniteDetermination

/-- The affine coefficient half-space for the `n`th coefficient in cusp coordinates. -/
noncomputable def coefficientHalfspace (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (n : ℕ) : Set (RealCuspForm.Coordinates.Space (k : ℤ)) :=
  FiniteHalfspace.halfspace
    (EisensteinDecomposition.eisensteinCoeff k hkpos hk4)
    (RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ))) n

/-- The coordinate vectors satisfying the coefficient inequalities indexed by `I`. -/
noncomputable def finiteNonnegativeCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (I : Finset ℕ) :
    Set (RealCuspForm.Coordinates.Space (k : ℤ)) :=
  FiniteHalfspace.finiteIntersection
    (EisensteinDecomposition.eisensteinCoeff k hkpos hk4)
    (RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ))) I

/-- The coordinate model of the normalized forms whose complete coefficient sequence is
nonnegative. -/
noncomputable def nonnegativeCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) : Set (RealCuspForm.Coordinates.Space (k : ℤ)) :=
  FiniteHalfspace.fullIntersection
    (EisensteinDecomposition.eisensteinCoeff k hkpos hk4)
    (RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ)))

@[simp] theorem mem_coefficientHalfspace (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (n : ℕ) (v : RealCuspForm.Coordinates.Space (k : ℤ)) :
    v ∈ coefficientHalfspace k hkpos hk4 n ↔
      0 ≤ EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n +
        RealCuspForm.Coordinates.coeffContinuous n v :=
  Iff.rfl

@[simp] theorem mem_finiteNonnegativeCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (I : Finset ℕ)
    (v : RealCuspForm.Coordinates.Space (k : ℤ)) :
    v ∈ finiteNonnegativeCoordinates k hkpos hk4 I ↔
      ∀ n ∈ I, v ∈ coefficientHalfspace k hkpos hk4 n :=
  Iff.rfl

@[simp] theorem mem_nonnegativeCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (v : RealCuspForm.Coordinates.Space (k : ℤ)) :
    v ∈ nonnegativeCoordinates k hkpos hk4 ↔
      ∀ n, v ∈ coefficientHalfspace k hkpos hk4 n :=
  Iff.rfl

/-- The normalized modular form represented by a cusp-coordinate vector. -/
noncomputable def formOfCoordinates (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (v : RealCuspForm.Coordinates.Space (k : ℤ)) :
    NormalizedRealModularForm (k : ℤ) := by
  refine ⟨EisensteinDecomposition.eisenstein k hkpos hk4 +
    RealCuspForm.toRealModularForm (RealCuspForm.Coordinates.toForm (k : ℤ) v), ?_⟩
  change RealModularForm.coeffLinear 0
    (EisensteinDecomposition.eisenstein k hkpos hk4 +
      RealCuspForm.toRealModularForm (RealCuspForm.Coordinates.toForm (k : ℤ) v)) = 1
  rw [map_add]
  simp

/-- The affine half-space formula is exactly the coefficient formula for the normalized form
represented by `v`. -/
theorem coeff_formOfCoordinates (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (v : RealCuspForm.Coordinates.Space (k : ℤ)) (n : ℕ) :
    NormalizedRealModularForm.coeff (formOfCoordinates k hkpos hk4 v) n =
      EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n +
        RealCuspForm.Coordinates.coeffContinuous n v := by
  change RealModularForm.coeffLinear n
    (EisensteinDecomposition.eisenstein k hkpos hk4 +
      RealCuspForm.toRealModularForm (RealCuspForm.Coordinates.toForm (k : ℤ) v)) = _
  rw [map_add]
  rfl

/-- The cusp-coordinate map recovers the vector used to construct a normalized form. -/
@[simp] theorem cuspCoordinates_formOfCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (v : RealCuspForm.Coordinates.Space (k : ℤ)) :
    EisensteinDecomposition.cuspCoordinates k hkpos hk4
      (formOfCoordinates k hkpos hk4 v) = v := by
  apply (RealCuspForm.Coordinates.toForm (k : ℤ)).injective
  apply RealCuspForm.toRealModularForm_injective
  apply add_left_cancel (a := EisensteinDecomposition.eisenstein k hkpos hk4)
  calc
    EisensteinDecomposition.eisenstein k hkpos hk4 +
        RealCuspForm.toRealModularForm
          (RealCuspForm.Coordinates.toForm (k : ℤ)
            (EisensteinDecomposition.cuspCoordinates k hkpos hk4
              (formOfCoordinates k hkpos hk4 v))) =
      (formOfCoordinates k hkpos hk4 v).1 :=
        (EisensteinDecomposition.eq_eisenstein_add_coordinates k hkpos hk4
          (formOfCoordinates k hkpos hk4 v)).symm
    _ = EisensteinDecomposition.eisenstein k hkpos hk4 +
        RealCuspForm.toRealModularForm
          (RealCuspForm.Coordinates.toForm (k : ℤ) v) := rfl

/-- Constructing a form from the cusp coordinates of a normalized form recovers that form. -/
@[simp] theorem formOfCoordinates_cuspCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (f : NormalizedRealModularForm (k : ℤ)) :
    formOfCoordinates k hkpos hk4
      (EisensteinDecomposition.cuspCoordinates k hkpos hk4 f) = f := by
  apply Subtype.ext
  exact (EisensteinDecomposition.eq_eisenstein_add_coordinates k hkpos hk4 f).symm

/-- The Task 4 coordinate space parametrizes the complete normalized real affine slice. -/
noncomputable def normalizedFormsEquivCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    NormalizedRealModularForm (k : ℤ) ≃ RealCuspForm.Coordinates.Space (k : ℤ) where
  toFun := EisensteinDecomposition.cuspCoordinates k hkpos hk4
  invFun := formOfCoordinates k hkpos hk4
  left_inv := formOfCoordinates_cuspCoordinates k hkpos hk4
  right_inv := cuspCoordinates_formOfCoordinates k hkpos hk4

/-- Membership in the `n`th affine half-space is precisely nonnegativity of the `n`th
coefficient. -/
theorem cuspCoordinates_mem_coefficientHalfspace_iff (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (f : NormalizedRealModularForm (k : ℤ)) (n : ℕ) :
    EisensteinDecomposition.cuspCoordinates k hkpos hk4 f ∈
        coefficientHalfspace k hkpos hk4 n ↔
      0 ≤ NormalizedRealModularForm.coeff f n := by
  rw [mem_coefficientHalfspace,
    EisensteinDecomposition.coeff_eq_eisenstein_add_coordinate]

/-- The full coordinate intersection corresponds exactly to coefficientwise nonnegativity. -/
theorem cuspCoordinates_mem_nonnegativeCoordinates_iff (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (f : NormalizedRealModularForm (k : ℤ)) :
    EisensteinDecomposition.cuspCoordinates k hkpos hk4 f ∈
        nonnegativeCoordinates k hkpos hk4 ↔
      ∀ n, 0 ≤ NormalizedRealModularForm.coeff f n := by
  simp only [mem_nonnegativeCoordinates,
    cuspCoordinates_mem_coefficientHalfspace_iff]

/-- The index-zero affine inequality is automatic: both coordinate descriptions are normalized
at constant coefficient one. -/
theorem mem_coefficientHalfspace_zero (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (v : RealCuspForm.Coordinates.Space (k : ℤ)) :
    v ∈ coefficientHalfspace k hkpos hk4 0 := by
  rw [mem_coefficientHalfspace]
  change 0 ≤ RealModularForm.coeff
      (EisensteinDecomposition.eisenstein k hkpos hk4) 0 +
    RealCuspForm.coeff (RealCuspForm.Coordinates.toForm (k : ℤ) v) 0
  simp

private theorem detects (k : ℕ) (hkpos : 0 < k) :
    ∀ v : RealCuspForm.Coordinates.Space (k : ℤ), v ≠ 0 →
      ∃ n : ℕ, RealCuspForm.Coordinates.coeffContinuous n v < 0 := by
  have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hkpos
  exact RealCuspForm.Coordinates.detects_nonzero_direction hkz

/-- The full nonnegative-coordinate set is closed. -/
theorem isClosed_nonnegativeCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    IsClosed (nonnegativeCoordinates k hkpos hk4) := by
  exact FiniteHalfspace.isClosed_fullIntersection
    (EisensteinDecomposition.eisensteinCoeff k hkpos hk4)
    (RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ)))

/-- The full nonnegative-coordinate set is convex. -/
theorem convex_nonnegativeCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    Convex ℝ (nonnegativeCoordinates k hkpos hk4) := by
  exact FiniteHalfspace.convex_fullIntersection
    (EisensteinDecomposition.eisensteinCoeff k hkpos hk4)
    (RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ)))

/-- The sign-change theorem blocks every nonzero cusp direction, so the full
nonnegative-coordinate set is bounded. -/
theorem isBounded_nonnegativeCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    Bornology.IsBounded (nonnegativeCoordinates k hkpos hk4) := by
  exact FiniteHalfspace.isBounded_fullIntersection_of_detects
    (EisensteinDecomposition.eisensteinCoeff k hkpos hk4)
    (RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ)))
    (detects k hkpos)

/-- The full nonnegative-coordinate set is compact. -/
theorem isCompact_nonnegativeCoordinates (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    IsCompact (nonnegativeCoordinates k hkpos hk4) := by
  exact FiniteHalfspace.isCompact_fullIntersection_of_detects
    (EisensteinDecomposition.eisensteinCoeff k hkpos hk4)
    (RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ)))
    (detects k hkpos)

/-- The Section 4 nonnegative-coordinate set is the intersection of finitely many
positive-index coefficient half-spaces.  The finite intersection is bounded, compact, and
convex, giving the precise mathlib formulation of a bounded finite convex polytope. -/
theorem exists_bounded_finite_convex_polytope (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    ∃ A : Finset ℕ,
      (∀ n ∈ A, 0 < n) ∧
      Bornology.IsBounded (finiteNonnegativeCoordinates k hkpos hk4 A) ∧
      IsCompact (finiteNonnegativeCoordinates k hkpos hk4 A) ∧
      Convex ℝ (finiteNonnegativeCoordinates k hkpos hk4 A) ∧
      finiteNonnegativeCoordinates k hkpos hk4 A =
        nonnegativeCoordinates k hkpos hk4 := by
  let e := EisensteinDecomposition.eisensteinCoeff k hkpos hk4
  let b := RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ))
  obtain ⟨I, _, hIfull⟩ := FiniteHalfspace.exists_finite_reduction e b
    (detects k hkpos)
    (EisensteinDomination.eventuallyContainsClosedBalls k hkpos hk4)
  let A : Finset ℕ := I.erase 0
  have hApos : ∀ n ∈ A, 0 < n := by
    intro n hn
    exact Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hn)
  have hAfull : FiniteHalfspace.finiteIntersection e b A =
      FiniteHalfspace.fullIntersection e b := by
    apply Set.Subset.antisymm
    · intro v hv
      rw [← hIfull]
      intro n hnI
      by_cases hn0 : n = 0
      · subst n
        exact mem_coefficientHalfspace_zero k hkpos hk4 v
      · exact hv n (Finset.mem_erase.mpr ⟨hn0, hnI⟩)
    · exact FiniteHalfspace.fullIntersection_subset_finiteIntersection e b A
  have hbounded : Bornology.IsBounded (FiniteHalfspace.finiteIntersection e b A) := by
    rw [hAfull]
    exact isBounded_nonnegativeCoordinates k hkpos hk4
  have hcompact : IsCompact (FiniteHalfspace.finiteIntersection e b A) := by
    rw [hAfull]
    exact isCompact_nonnegativeCoordinates k hkpos hk4
  have hconvex : Convex ℝ (FiniteHalfspace.finiteIntersection e b A) :=
    FiniteHalfspace.convex_finiteIntersection e b A
  exact ⟨A, hApos, hbounded, hcompact, hconvex, hAfull⟩

/-- The finite-set coefficient test corresponding directly to Theorem 5 of the paper.  All
indices in the witness are positive; the normalized constant coefficient is not included. -/
theorem exists_finite_coefficient_test_levelOne (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    ∃ A : Finset ℕ,
      (∀ n ∈ A, 0 < n) ∧
      ∀ f : NormalizedRealModularForm (k : ℤ),
        ((∀ n ∈ A, 0 ≤ NormalizedRealModularForm.coeff f n) ↔
          ∀ n, 0 ≤ NormalizedRealModularForm.coeff f n) := by
  obtain ⟨A, hApos, _, _, _, hAfull⟩ :=
    exists_bounded_finite_convex_polytope k hkpos hk4
  refine ⟨A, hApos, ?_⟩
  intro f
  constructor
  · intro hfinite
    apply (cuspCoordinates_mem_nonnegativeCoordinates_iff k hkpos hk4 f).mp
    rw [← hAfull, mem_finiteNonnegativeCoordinates]
    intro n hn
    rw [cuspCoordinates_mem_coefficientHalfspace_iff]
    exact hfinite n hn
  · intro hall n _
    exact hall n

/-- Initial-segment form of the coefficient test.  The upper endpoint is inclusive and only
positive indices are assumed; coefficient zero is automatic from normalization. -/
theorem exists_initial_coefficient_test_levelOne (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    ∃ N : ℕ, ∀ f : NormalizedRealModularForm (k : ℤ),
      ((∀ n, 1 ≤ n → n ≤ N → 0 ≤ NormalizedRealModularForm.coeff f n) ↔
        ∀ n, 0 ≤ NormalizedRealModularForm.coeff f n) := by
  let e := EisensteinDecomposition.eisensteinCoeff k hkpos hk4
  let b := RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ))
  obtain ⟨N, _, hNfull⟩ := FiniteHalfspace.exists_initialSegment_reduction e b
    (detects k hkpos)
    (EisensteinDomination.eventuallyContainsClosedBalls k hkpos hk4)
  refine ⟨N, ?_⟩
  intro f
  constructor
  · intro hinitial
    apply (cuspCoordinates_mem_nonnegativeCoordinates_iff k hkpos hk4 f).mp
    change EisensteinDecomposition.cuspCoordinates k hkpos hk4 f ∈
      FiniteHalfspace.fullIntersection e b
    rw [← hNfull]
    intro n hn
    change EisensteinDecomposition.cuspCoordinates k hkpos hk4 f ∈
      coefficientHalfspace k hkpos hk4 n
    rw [cuspCoordinates_mem_coefficientHalfspace_iff]
    by_cases hn0 : n = 0
    · subst n
      simp
    · exact hinitial n (Nat.one_le_iff_ne_zero.mpr hn0)
        (Nat.le_of_lt (Finset.mem_range.mp hn))
  · intro hall n _ _
    exact hall n

/-- User-facing well-definedness statement: there is a finite nonnegativity bound for normalized
real level-one modular forms in every positive weight divisible by four. -/
theorem exists_nonnegativity_bound_levelOne (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    ∃ N : ℕ, ∀ f : NormalizedRealModularForm (k : ℤ),
      (∀ n, 1 ≤ n → n ≤ N → 0 ≤ NormalizedRealModularForm.coeff f n) →
        ∀ n, 0 ≤ NormalizedRealModularForm.coeff f n := by
  obtain ⟨N, hN⟩ := exists_initial_coefficient_test_levelOne k hkpos hk4
  exact ⟨N, fun f hinitial ↦ (hN f).mp hinitial⟩

/-- Equivalently, if a normalized form has any negative coefficient, then it already has one at
a positive index bounded uniformly in terms of the weight. -/
theorem exists_bounded_negative_witness_levelOne (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    ∃ N : ℕ, ∀ f : NormalizedRealModularForm (k : ℤ),
      (∃ n, NormalizedRealModularForm.coeff f n < 0) →
        ∃ n, 1 ≤ n ∧ n ≤ N ∧ NormalizedRealModularForm.coeff f n < 0 := by
  obtain ⟨N, hN⟩ := exists_nonnegativity_bound_levelOne k hkpos hk4
  refine ⟨N, ?_⟩
  intro f hnegative
  by_contra hbounded
  have hinitial : ∀ n, 1 ≤ n → n ≤ N →
      0 ≤ NormalizedRealModularForm.coeff f n := by
    intro n hnpos hnN
    exact le_of_not_gt fun hnneg ↦ hbounded ⟨n, hnpos, hnN, hnneg⟩
  have hall := hN f hinitial
  obtain ⟨n, hn⟩ := hnegative
  exact (not_lt_of_ge (hall n)) hn

end FiniteDetermination

end Section4.RealForms
