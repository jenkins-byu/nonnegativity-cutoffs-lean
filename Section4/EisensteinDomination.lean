import Section4.EisensteinPositivity
import Section4.FiniteHalfspace
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# Uniform Eisenstein domination on bounded cusp-coordinate sets

This file turns mathlib's pointwise Hecke bound for each cusp form into a bound uniform over
bounded subsets of the finite Euclidean coordinate space chosen in `Section4.RealForms`.  It then
combines that estimate with the Eisenstein lower growth from Task 7 to discharge the eventual
closed-ball containment hypothesis of the abstract finite-half-space theorem.
-/

open Filter Metric Set Asymptotics
open scoped MatrixGroups UpperHalfPlane Topology

namespace Section4.RealForms

open UpperHalfPlane

namespace EisensteinDomination

/-- The real-power comparison function in mathlib's Hecke bound for weight `k`. -/
noncomputable def cuspGrowth (k n : ℕ) : ℝ :=
  (n : ℝ) ^ (((k : ℤ) : ℝ) / 2)

/-- The real coefficients of an individual real cusp form satisfy Hecke's pointwise
`O(n^(k/2))` bound. -/
theorem cuspCoeff_isBigO (k : ℕ) (f : RealCuspForm (k : ℤ)) :
    (fun n ↦ RealCuspForm.coeff f n) =O[atTop] cuspGrowth k := by
  let complexCoeff : ℕ → ℂ :=
    fun n ↦ (qExpansion 1 (f : CuspForm 𝒮ℒ (k : ℤ))).coeff n
  have hre : (fun n ↦ RealCuspForm.coeff f n) =O[atTop] complexCoeff := by
    apply IsBigO.of_bound'
    filter_upwards [] with n
    change |(complexCoeff n).re| ≤ ‖complexCoeff n‖
    exact Complex.abs_re_le_norm _
  have hcomplex : complexCoeff =O[atTop] cuspGrowth k := by
    change complexCoeff =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (((k : ℤ) : ℝ) / 2))
    simpa only [complexCoeff, Subgroup.strictWidthInfty_SL2Z] using
      (CuspFormClass.qExpansion_isBigO (f : CuspForm 𝒮ℒ (k : ℤ)))
  exact hre.trans hcomplex

/-- The `i`th standard coordinate vector in the Task 4 Euclidean cusp model. -/
noncomputable def basisVector (k : ℕ)
    (i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ))) :
    RealCuspForm.Coordinates.Space (k : ℤ) :=
  Pi.single i 1

/-- The coefficient sequence of the cusp form represented by the `i`th standard coordinate
vector. -/
noncomputable def basisCoeff (k : ℕ)
    (i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ))) (n : ℕ) : ℝ :=
  RealCuspForm.Coordinates.coeffContinuous n (basisVector k i)

/-- The sum of the absolute values of all standard-coordinate coefficient sequences at `n`. -/
noncomputable def basisAbsSum (k n : ℕ) : ℝ :=
  ∑ i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ)), |basisCoeff k i n|

theorem basisCoeff_isBigO (k : ℕ)
    (i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ))) :
    basisCoeff k i =O[atTop] cuspGrowth k := by
  change (fun n ↦ RealCuspForm.coeff
    (RealCuspForm.Coordinates.toForm (k : ℤ) (Pi.single i 1)) n) =O[atTop] cuspGrowth k
  exact cuspCoeff_isBigO k
    (RealCuspForm.Coordinates.toForm (k : ℤ) (Pi.single i 1))

theorem basisAbsSum_isBigO (k : ℕ) :
    basisAbsSum k =O[atTop] cuspGrowth k := by
  change (fun n ↦ ∑ i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ)),
    |basisCoeff k i n|) =O[atTop] cuspGrowth k
  refine (IsBigO.sum (s := Finset.univ)
    fun i _ ↦ (basisCoeff_isBigO k i).abs_left).congr_left ?_
  intro n
  simp only [Finset.sum_apply]

/-- A coordinate coefficient is the corresponding linear combination of the coefficients of the
standard coordinate vectors. -/
theorem coeffContinuous_eq_sum (k n : ℕ)
    (v : RealCuspForm.Coordinates.Space (k : ℤ)) :
    RealCuspForm.Coordinates.coeffContinuous n v =
      ∑ i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ)), v i * basisCoeff k i n := by
  conv_lhs => rw [pi_eq_sum_univ' v, map_sum]
  simp only [map_smul, basisCoeff, basisVector, smul_eq_mul]

/-- The absolute value of any coordinate coefficient is bounded by the coordinate norm times the
finite sum of the absolute values of the standard-coordinate coefficients. -/
theorem abs_coeffContinuous_le_norm_mul_basisAbsSum (k n : ℕ)
    (v : RealCuspForm.Coordinates.Space (k : ℤ)) :
    |RealCuspForm.Coordinates.coeffContinuous n v| ≤ ‖v‖ * basisAbsSum k n := by
  rw [coeffContinuous_eq_sum]
  calc
    |∑ i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ)), v i * basisCoeff k i n| ≤
        ∑ i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ)),
          |v i * basisCoeff k i n| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ)),
          |v i| * |basisCoeff k i n| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul]
    _ ≤ ∑ i : Fin (RealCuspForm.Coordinates.dimension (k : ℤ)),
          ‖v‖ * |basisCoeff k i n| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (abs_nonneg _)
    _ = ‖v‖ * basisAbsSum k n := by
      simp only [basisAbsSum, Finset.mul_sum]

theorem basisAbsSum_nonneg (k n : ℕ) : 0 ≤ basisAbsSum k n := by
  exact Finset.sum_nonneg fun i _ ↦ abs_nonneg (basisCoeff k i n)

/-- At an admissible weight, the real exponent in the cusp bound is the natural exponent
`k / 2`. -/
theorem cuspGrowth_eq_pow (k : ℕ) (hk4 : k % 4 = 0) (n : ℕ) :
    cuspGrowth k n = (n : ℝ) ^ (k / 2) := by
  have hk2 : 2 ∣ k := by omega
  change (n : ℝ) ^ ((k : ℝ) / 2) = (n : ℝ) ^ (k / 2)
  have hhalf : (k : ℝ) / 2 = ((k / 2 : ℕ) : ℝ) := by
    apply (div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    norm_cast
    omega
  rw [hhalf, Real.rpow_natCast]

theorem half_nat_lt_sub_one (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    k / 2 < k - 1 := by
  have hkge : 4 ≤ k := AdmissibleWeight.four_le hkpos hk4
  omega

/-- The cusp-form comparison function is little-oh of the Eisenstein polynomial power. -/
theorem cuspGrowth_isLittleO_eisensteinPower (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    cuspGrowth k =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (k - 1)) := by
  have hreal : (fun x : ℝ ↦ x ^ (k / 2)) =o[atTop] (fun x : ℝ ↦ x ^ (k - 1)) :=
    Asymptotics.isLittleO_pow_pow_atTop_of_lt (half_nat_lt_sub_one k hkpos hk4)
  have hnat := hreal.comp_tendsto tendsto_natCast_atTop_atTop
  change (fun n : ℕ ↦ (n : ℝ) ^ (k / 2)) =o[atTop]
    (fun n : ℕ ↦ (n : ℝ) ^ (k - 1)) at hnat
  rw [show cuspGrowth k = (fun n : ℕ ↦ (n : ℝ) ^ (k / 2)) by
    funext n
    exact cuspGrowth_eq_pow k hk4 n]
  exact hnat

/-- The single finite envelope of all coordinate-basis coefficients is little-oh of the
Eisenstein polynomial power. -/
theorem basisAbsSum_isLittleO_eisensteinPower (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    basisAbsSum k =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (k - 1)) :=
  (basisAbsSum_isBigO k).trans_isLittleO
    (cuspGrowth_isLittleO_eisensteinPower k hkpos hk4)

/-- On a fixed coordinate ball of radius `R`, the common basis-coefficient envelope is eventually
smaller than the Eisenstein coefficient. -/
theorem eventually_radius_mul_basisAbsSum_le_eisensteinCoeff (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ n in atTop,
      R * basisAbsSum k n ≤ EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n := by
  have hsmall :=
    ((basisAbsSum_isLittleO_eisensteinPower k hkpos hk4).const_mul_left R).def
      (EisensteinPositivity.eisensteinScale_pos k hkpos hk4)
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnpos
  have hleft : 0 ≤ R * basisAbsSum k n :=
    mul_nonneg hR (basisAbsSum_nonneg k n)
  have hpower : 0 ≤ (n : ℝ) ^ (k - 1) := by positivity
  have hcomparison :
      R * basisAbsSum k n ≤
        EisensteinPositivity.eisensteinScale k * (n : ℝ) ^ (k - 1) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hpower] using hn
  exact hcomparison.trans
    (EisensteinPositivity.scale_mul_pow_le_eisensteinCoeff k hkpos hk4 n hnpos)

/-- A quantitative form of uniform domination: once the basis envelope is dominated at index
`n`, every cusp coordinate vector in the closed ball of radius `R` has coefficient of absolute
value at most the Eisenstein coefficient. -/
theorem abs_coeffContinuous_le_eisensteinCoeff_of_mem_closedBall (k : ℕ)
    (hkpos : 0 < k) (hk4 : k % 4 = 0) (R : ℝ) (n : ℕ)
    (henvelope :
      R * basisAbsSum k n ≤ EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n)
    (v : RealCuspForm.Coordinates.Space (k : ℤ)) (hv : v ∈ closedBall 0 R) :
    |RealCuspForm.Coordinates.coeffContinuous n v| ≤
      EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n := by
  have hvnorm : ‖v‖ ≤ R := by
    simpa only [mem_closedBall, dist_zero_right] using hv
  exact (abs_coeffContinuous_le_norm_mul_basisAbsSum k n v).trans
    ((mul_le_mul_of_nonneg_right hvnorm (basisAbsSum_nonneg k n)).trans henvelope)

/-- For every nonnegative radius, all sufficiently late normalized Eisenstein-plus-cusp
coefficients are nonnegative, uniformly over the corresponding coordinate ball. -/
theorem eventually_nonneg_on_closedBall (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ n in atTop, ∀ v : RealCuspForm.Coordinates.Space (k : ℤ),
      v ∈ closedBall 0 R →
        0 ≤ EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n +
          RealCuspForm.Coordinates.coeffContinuous n v := by
  filter_upwards
    [eventually_radius_mul_basisAbsSum_le_eisensteinCoeff k hkpos hk4 R hR]
      with n hn
  intro v hv
  have habs := abs_coeffContinuous_le_eisensteinCoeff_of_mem_closedBall
    k hkpos hk4 R n hn v hv
  linarith [neg_le_of_abs_le habs]

/-- The exact eventual-tail hypothesis required by `FiniteHalfspace.exists_finite_reduction` for
the Task 4 Euclidean coordinate model. -/
theorem eventuallyContainsClosedBalls (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    FiniteHalfspace.EventuallyContainsClosedBalls
      (EisensteinDecomposition.eisensteinCoeff k hkpos hk4)
      (RealCuspForm.Coordinates.coeffContinuous (k := (k : ℤ))) := by
  intro R hR
  filter_upwards [eventually_nonneg_on_closedBall k hkpos hk4 R hR] with n hn
  intro v hv
  exact hn v hv

end EisensteinDomination

end Section4.RealForms
