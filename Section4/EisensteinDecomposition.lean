import Section4.RealForms
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The normalized Eisenstein-cusp decomposition

For a positive level-one weight divisible by four, this file packages the normalized Eisenstein
series as a real modular form and identifies the normalized affine slice with the real cusp-form
space.  The invariant decomposition is proved first and then transported to the noncomputable
Euclidean coordinates chosen in `Section4.RealForms`.
-/

open scoped MatrixGroups UpperHalfPlane

namespace Section4.RealForms

open UpperHalfPlane

namespace AdmissibleWeight

/-- Divisibility by four expressed from the public remainder hypothesis. -/
theorem four_dvd {k : ℕ} (hk4 : k % 4 = 0) : 4 ∣ k :=
  Nat.dvd_of_mod_eq_zero hk4

/-- A positive natural number divisible by four is at least four. -/
theorem four_le {k : ℕ} (hkpos : 0 < k) (hk4 : k % 4 = 0) : 4 ≤ k :=
  Nat.le_of_dvd hkpos (four_dvd hk4)

/-- The lower bound required to construct the normalized Eisenstein series in mathlib. -/
theorem three_le {k : ℕ} (hkpos : 0 < k) (hk4 : k % 4 = 0) : 3 ≤ k :=
  (by omega : 3 ≤ 4).trans (four_le hkpos hk4)

/-- A natural number divisible by four is even. -/
theorem even {k : ℕ} (hk4 : k % 4 = 0) : Even k := by
  rw [even_iff_two_dvd]
  exact (by norm_num : 2 ∣ 4).trans (four_dvd hk4)

end AdmissibleWeight

namespace RealModularForm

variable {k : ℤ}

/-- A real q-expansion coefficient, regarded as a complex number, is the original complex
coefficient. -/
theorem qExpansion_coeff_eq_coe (f : RealModularForm k) (n : ℕ) :
    (qExpansion 1 (f : ModularForm 𝒮ℒ k)).coeff n = (coeff f n : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using f.property n

end RealModularForm

namespace EisensteinDecomposition

/-- The normalized Eisenstein series, bundled as a real level-one modular form. -/
noncomputable def eisenstein (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    RealModularForm (k : ℤ) := by
  let hk3 : 3 ≤ k := AdmissibleWeight.three_le hkpos hk4
  let hk2 : Even k := AdmissibleWeight.even hk4
  refine ⟨ModularForm.E hk3, ?_⟩
  intro n
  rw [EisensteinSeries.E_qExpansion_coeff hk3 hk2]
  split_ifs <;> simp

@[simp] theorem eisenstein_coeff_zero (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    RealModularForm.coeff (eisenstein k hkpos hk4) 0 = 1 := by
  change ((qExpansion 1 (ModularForm.E (AdmissibleWeight.three_le hkpos hk4))).coeff 0).re = 1
  rw [EisensteinSeries.E_qExpansion_coeff_zero _ (AdmissibleWeight.even hk4)]
  simp

/-- The modular-form difference between a normalized form and the normalized Eisenstein
series.  Its constant coefficient is zero, so it comes from a cusp form. -/
noncomputable def cuspDifference (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (f : NormalizedRealModularForm (k : ℤ)) : RealModularForm (k : ℤ) :=
  f.1 - eisenstein k hkpos hk4

@[simp] theorem cuspDifference_coeff (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (f : NormalizedRealModularForm (k : ℤ)) (n : ℕ) :
    RealModularForm.coeff (cuspDifference k hkpos hk4 f) n =
      NormalizedRealModularForm.coeff f n -
        RealModularForm.coeff (eisenstein k hkpos hk4) n := by
  simpa [cuspDifference, NormalizedRealModularForm.coeff] using
    map_sub (RealModularForm.coeffLinear (k := (k : ℤ)) n) f.1
      (eisenstein k hkpos hk4)

@[simp] theorem cuspDifference_coeff_zero (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (f : NormalizedRealModularForm (k : ℤ)) :
    RealModularForm.coeff (cuspDifference k hkpos hk4 f) 0 = 0 := by
  rw [cuspDifference_coeff, NormalizedRealModularForm.coeff_zero,
    eisenstein_coeff_zero, sub_self]

private theorem cuspDifference_qExpansion_coeff_zero (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (f : NormalizedRealModularForm (k : ℤ)) :
    (qExpansion 1 (cuspDifference k hkpos hk4 f).1).coeff 0 = 0 := by
  rw [RealModularForm.qExpansion_coeff_eq_coe]
  simp

/-- The cusp part of a normalized real modular form, obtained from its zero-constant-term
difference with the normalized Eisenstein series. -/
noncomputable def cuspPart (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (f : NormalizedRealModularForm (k : ℤ)) : RealCuspForm (k : ℤ) := by
  refine ⟨ModularForm.toCuspForm
    (cuspDifference k hkpos hk4 f).1
    (cuspDifference_qExpansion_coeff_zero k hkpos hk4 f), ?_⟩
  intro n
  exact (cuspDifference k hkpos hk4 f).property n

@[simp] theorem cuspPart_toRealModularForm (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (f : NormalizedRealModularForm (k : ℤ)) :
    RealCuspForm.toRealModularForm (cuspPart k hkpos hk4 f) =
      cuspDifference k hkpos hk4 f := by
  apply Subtype.ext
  apply ModularForm.ext
  intro z
  simp [cuspPart]

/-- Every normalized real modular form is the normalized Eisenstein series plus its cusp
part.  This statement is independent of any basis of the cusp-form space. -/
theorem eq_eisenstein_add_cuspPart (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (f : NormalizedRealModularForm (k : ℤ)) :
    f.1 = eisenstein k hkpos hk4 +
      RealCuspForm.toRealModularForm (cuspPart k hkpos hk4 f) := by
  rw [cuspPart_toRealModularForm]
  simp [cuspDifference]

/-- The Eisenstein-cusp decomposition of a normalized real modular form exists uniquely. -/
theorem existsUnique_cuspPart (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (f : NormalizedRealModularForm (k : ℤ)) :
    ∃! g : RealCuspForm (k : ℤ),
      f.1 = eisenstein k hkpos hk4 + RealCuspForm.toRealModularForm g := by
  refine ⟨cuspPart k hkpos hk4 f, eq_eisenstein_add_cuspPart k hkpos hk4 f, ?_⟩
  intro g hg
  apply RealCuspForm.toRealModularForm_injective
  apply add_left_cancel (a := eisenstein k hkpos hk4)
  exact hg.symm.trans (eq_eisenstein_add_cuspPart k hkpos hk4 f)

/-- The coordinates of the cusp part in the noncomputably chosen Euclidean model from
`Section4.RealForms`. -/
noncomputable def cuspCoordinates (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (f : NormalizedRealModularForm (k : ℤ)) :
    RealCuspForm.Coordinates.Space (k : ℤ) :=
  RealCuspForm.Coordinates.ofForm (k : ℤ) (cuspPart k hkpos hk4 f)

@[simp] theorem coordinates_to_cuspPart (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (f : NormalizedRealModularForm (k : ℤ)) :
    RealCuspForm.Coordinates.toForm (k : ℤ) (cuspCoordinates k hkpos hk4 f) =
      cuspPart k hkpos hk4 f := by
  simp [cuspCoordinates]

/-- The invariant Eisenstein-cusp decomposition transported to Euclidean coordinates. -/
theorem eq_eisenstein_add_coordinates (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (f : NormalizedRealModularForm (k : ℤ)) :
    f.1 = eisenstein k hkpos hk4 + RealCuspForm.toRealModularForm
      (RealCuspForm.Coordinates.toForm (k : ℤ) (cuspCoordinates k hkpos hk4 f)) := by
  rw [coordinates_to_cuspPart]
  exact eq_eisenstein_add_cuspPart k hkpos hk4 f

/-- The Euclidean coordinate vector in the Eisenstein-cusp decomposition is unique. -/
theorem existsUnique_coordinates (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (f : NormalizedRealModularForm (k : ℤ)) :
    ∃! v : RealCuspForm.Coordinates.Space (k : ℤ),
      f.1 = eisenstein k hkpos hk4 + RealCuspForm.toRealModularForm
        (RealCuspForm.Coordinates.toForm (k : ℤ) v) := by
  refine ⟨cuspCoordinates k hkpos hk4 f,
    eq_eisenstein_add_coordinates k hkpos hk4 f, ?_⟩
  intro v hv
  apply (RealCuspForm.Coordinates.toForm (k : ℤ)).injective
  apply RealCuspForm.toRealModularForm_injective
  apply add_left_cancel (a := eisenstein k hkpos hk4)
  exact hv.symm.trans (eq_eisenstein_add_coordinates k hkpos hk4 f)

/-- The `n`th coefficient of the normalized Eisenstein series, isolated as the fixed affine
term in the coefficient formula. -/
noncomputable def eisensteinCoeff (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (n : ℕ) : ℝ :=
  RealModularForm.coeff (eisenstein k hkpos hk4) n

/-- In cusp coordinates, every coefficient of a normalized form is the corresponding
Eisenstein coefficient plus the linear cusp coefficient functional. -/
theorem coeff_eq_eisenstein_add_coordinate (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (f : NormalizedRealModularForm (k : ℤ)) (n : ℕ) :
    NormalizedRealModularForm.coeff f n = eisensteinCoeff k hkpos hk4 n +
      RealCuspForm.Coordinates.coeffContinuous n (cuspCoordinates k hkpos hk4 f) := by
  calc
    NormalizedRealModularForm.coeff f n = RealModularForm.coeff f.1 n := rfl
    _ = RealModularForm.coeff
        (eisenstein k hkpos hk4 + RealCuspForm.toRealModularForm
          (RealCuspForm.Coordinates.toForm (k : ℤ) (cuspCoordinates k hkpos hk4 f))) n :=
      congrArg (fun F : RealModularForm (k : ℤ) ↦ RealModularForm.coeff F n)
        (eq_eisenstein_add_coordinates k hkpos hk4 f)
    _ = RealModularForm.coeff (eisenstein k hkpos hk4) n +
        RealCuspForm.coeff
          (RealCuspForm.Coordinates.toForm (k : ℤ) (cuspCoordinates k hkpos hk4 f)) n := by
      change RealModularForm.coeffLinear n
          (eisenstein k hkpos hk4 + RealCuspForm.toRealModularForm
            (RealCuspForm.Coordinates.toForm (k : ℤ) (cuspCoordinates k hkpos hk4 f))) = _
      rw [map_add]
      rfl
    _ = eisensteinCoeff k hkpos hk4 n +
        RealCuspForm.Coordinates.coeffContinuous n (cuspCoordinates k hkpos hk4 f) := by
      rfl

end EisensteinDecomposition

end Section4.RealForms
