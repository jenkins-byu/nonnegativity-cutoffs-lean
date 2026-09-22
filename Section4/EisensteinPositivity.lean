import Section4.EisensteinDecomposition
import Mathlib.NumberTheory.ZetaValues

/-!
# Positivity and lower growth of normalized Eisenstein coefficients

For a positive level-one weight divisible by four, this file proves the sign of the relevant
Bernoulli number, positivity of every positive-index coefficient of the normalized Eisenstein
series, and a quantitative polynomial lower bound.  These are the arithmetic inputs for the
later uniform comparison with cusp coefficients.
-/

open scoped MatrixGroups UpperHalfPlane

namespace Section4.RealForms

open UpperHalfPlane

namespace EisensteinPositivity

/-- The Bernoulli number in a positive weight divisible by four is negative. -/
theorem bernoulli_neg (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) : bernoulli k < 0 := by
  obtain ⟨m, rfl⟩ := AdmissibleWeight.four_dvd hk4
  have hm : m ≠ 0 := by omega
  have hsum := hasSum_zeta_nat (k := 2 * m) (by omega)
  have hpos : 0 < ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * (2 * m)) :=
    hsum.summable.tsum_pos (fun n ↦ by positivity) 1 (by norm_num)
  rw [hsum.tsum_eq] at hpos
  have htwo : 2 * (2 * m) = 4 * m := by omega
  have hsign : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [pow_succ]
    simp [pow_mul]
  rw [hsign, htwo] at hpos
  let C : ℝ :=
    (2 : ℝ) ^ (2 * (2 * m) - 1) * Real.pi ^ (2 * (2 * m)) /
      Nat.factorial (2 * (2 * m))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hproduct : 0 < -C * (bernoulli (4 * m) : ℝ) := by
    dsimp [C]
    rw [htwo]
    convert hpos using 1
    all_goals ring
  have hbern_real : (bernoulli (4 * m) : ℝ) < 0 := by
    nlinarith
  exact_mod_cast hbern_real

/-- The positive normalization factor multiplying the divisor sum in the nonconstant
coefficients of the normalized Eisenstein series. -/
noncomputable def eisensteinScale (k : ℕ) : ℝ :=
  -(2 * (k : ℝ) / (bernoulli k : ℝ))

theorem eisensteinScale_pos (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    0 < eisensteinScale k := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hbern : ((bernoulli k : ℚ) : ℝ) < 0 := by
    exact_mod_cast bernoulli_neg k hkpos hk4
  simp only [eisensteinScale]
  exact neg_pos.mpr (div_neg_of_pos_of_neg (mul_pos (by norm_num) hkreal) hbern)

/-- At a positive index, the normalized Eisenstein coefficient is its positive scale times the
divisor sum `σ_{k-1}(n)`. -/
theorem eisensteinCoeff_eq_scale_mul_sigma (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (n : ℕ) (hn : n ≠ 0) :
    EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n =
      eisensteinScale k * (ArithmeticFunction.sigma (k - 1) n : ℝ) := by
  change
    ((qExpansion 1 (ModularForm.E (AdmissibleWeight.three_le hkpos hk4))).coeff n).re = _
  rw [EisensteinSeries.E_qExpansion_coeff _ (AdmissibleWeight.even hk4)]
  simp [hn, eisensteinScale]

/-- Every positive-index coefficient of the normalized Eisenstein series is strictly positive. -/
theorem eisensteinCoeff_pos (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (n : ℕ) (hn : 0 < n) :
    0 < EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n := by
  rw [eisensteinCoeff_eq_scale_mul_sigma k hkpos hk4 n hn.ne']
  exact mul_pos (eisensteinScale_pos k hkpos hk4) (by
    exact_mod_cast ArithmeticFunction.sigma_pos (k - 1) n hn.ne')

/-- The divisor sum contains the divisor `n` itself, so it is at least `n^a`. -/
theorem pow_le_sigma (a n : ℕ) (hn : n ≠ 0) :
    n ^ a ≤ ArithmeticFunction.sigma a n := by
  rw [ArithmeticFunction.sigma_apply]
  exact Finset.single_le_sum (fun d _ ↦ Nat.zero_le (d ^ a))
    (Nat.mem_divisors_self n hn)

/-- Quantitative polynomial lower bound for every positive-index Eisenstein coefficient. -/
theorem scale_mul_pow_le_eisensteinCoeff (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (n : ℕ) (hn : 0 < n) :
    eisensteinScale k * (n : ℝ) ^ (k - 1) ≤
      EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n := by
  rw [eisensteinCoeff_eq_scale_mul_sigma k hkpos hk4 n hn.ne']
  apply mul_le_mul_of_nonneg_left _ (eisensteinScale_pos k hkpos hk4).le
  exact_mod_cast pow_le_sigma (k - 1) n hn.ne'

/-- The same lower bound with the exponent written as a real power, matching mathlib's cusp-form
coefficient-growth API. -/
theorem scale_mul_rpow_le_eisensteinCoeff (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (n : ℕ) (hn : 0 < n) :
    eisensteinScale k * (n : ℝ) ^ ((k : ℝ) - 1) ≤
      EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n := by
  have hkone : 1 ≤ k := hkpos
  rw [← Nat.cast_one, ← Nat.cast_sub hkone, Real.rpow_natCast]
  exact scale_mul_pow_le_eisensteinCoeff k hkpos hk4 n hn

/-- The Eisenstein exponent `k - 1` is strictly larger than the cusp-growth exponent `k / 2`
in every admissible weight. -/
theorem half_weight_lt_weight_sub_one (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    (k : ℝ) / 2 < (k : ℝ) - 1 := by
  have hkreal : (4 : ℝ) ≤ k := by
    exact_mod_cast AdmissibleWeight.four_le hkpos hk4
  linarith

/-- Qualitative lower growth in a form that hides the exact Bernoulli normalization: there is a
positive constant times `n^(k-1)` below every positive-index Eisenstein coefficient. -/
theorem exists_pos_scale_rpow_le_eisensteinCoeff (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      c * (n : ℝ) ^ ((k : ℝ) - 1) ≤
        EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n := by
  exact ⟨eisensteinScale k, eisensteinScale_pos k hkpos hk4,
    scale_mul_rpow_le_eisensteinCoeff k hkpos hk4⟩

end EisensteinPositivity

end Section4.RealForms
