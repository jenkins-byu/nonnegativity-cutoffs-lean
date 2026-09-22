import Section4.FiniteDetermination
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# The least nonnegativity bound `A(k)`

This file defines the least positive initial-segment bound detecting coefficientwise
nonnegativity, proves its specification, relates it to first negative coefficients, and extends
the normalized statement to arbitrary real level-one modular forms.
-/

open Set
open scoped MatrixGroups UpperHalfPlane

namespace Section4.RealForms

open UpperHalfPlane

namespace NonnegativityBound

private theorem qExpansion_mul_coeff_im_eq_zero {F G : Type*} [FunLike F ℍ ℂ]
    [FunLike G ℍ ℂ] {a b : ℤ} [ModularFormClass F 𝒮ℒ a]
    [ModularFormClass G 𝒮ℒ b] (f : F) (g : G)
    (hf : HasRealQExpansionAt 1 f) (hg : HasRealQExpansionAt 1 g) (n : ℕ) :
    ((qExpansion 1 ((⇑f * ⇑g : ℍ → ℂ))).coeff n).im = 0 := by
  have hf' (m : ℕ) : ((qExpansion 1 (⇑f : ℍ → ℂ)).coeff m).im = 0 := hf m
  have hg' (m : ℕ) : ((qExpansion 1 (⇑g : ℍ → ℂ)).coeff m).im = 0 := hg m
  rw [ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_mul]
  simp [Complex.mul_im, hf', hg']

/-- The product of coefficientwise-real modular forms is coefficientwise real. -/
private noncomputable def realModularMul {a b : ℤ}
    (f : RealModularForm a) (g : RealModularForm b) : RealModularForm (a + b) := by
  refine ⟨(f.1).mul g.1, ?_⟩
  intro n
  exact qExpansion_mul_coeff_im_eq_zero f.1 g.1 f.property g.property n

/-- Multiplication by a coefficientwise-real modular form preserves real cusp forms. -/
private noncomputable def realCuspMul {a b : ℤ}
    (f : RealCuspForm a) (g : RealModularForm b) : RealCuspForm (a + b) := by
  refine ⟨(f.1).mulModularForm g.1, ?_⟩
  intro n
  exact qExpansion_mul_coeff_im_eq_zero f.1 g.1 f.property g.property n

private noncomputable def realModularMcast {a b : ℤ} (hab : a = b)
    (f : RealModularForm a) : RealModularForm b := by
  refine ⟨ModularForm.mcast hab f.1, ?_⟩
  intro n
  change ((qExpansion 1 (f.1 : ℍ → ℂ)).coeff n).im = 0
  exact f.property n

private noncomputable def realCuspMcast {a b : ℤ} (hab : a = b)
    (f : RealCuspForm a) : RealCuspForm b := by
  refine ⟨CuspForm.mcast hab f.1, ?_⟩
  intro n
  change ((qExpansion 1 (f.1 : ℍ → ℂ)).coeff n).im = 0
  exact f.property n

/-- The normalized Eisenstein series of any even natural weight at least three has real
q-expansion.  This local generality is needed only for `E₆` in the construction of `Δ`. -/
private noncomputable def realEisensteinEven (k : ℕ) (hk3 : 3 ≤ k) (hkeven : Even k) :
    RealModularForm (k : ℤ) := by
  refine ⟨ModularForm.E hk3, ?_⟩
  intro n
  rw [EisensteinSeries.E_qExpansion_coeff hk3 hkeven]
  split_ifs <;> simp

private noncomputable def realE₄ : RealModularForm 4 :=
  realEisensteinEven 4 (by norm_num) ⟨2, rfl⟩

private noncomputable def realE₆ : RealModularForm 6 :=
  realEisensteinEven 6 (by norm_num) ⟨3, rfl⟩

private noncomputable def realE₄Cube : RealModularForm 12 :=
  realModularMcast (by norm_num)
    (realModularMul (realModularMul realE₄ realE₄) realE₄)

private noncomputable def realE₆Sq : RealModularForm 12 :=
  realModularMcast (by norm_num) (realModularMul realE₆ realE₆)

private noncomputable def realDiscriminantCandidate : RealModularForm 12 :=
  (1 / 1728 : ℝ) • (realE₄Cube - realE₆Sq)

/-- The modular discriminant has a coefficientwise-real q-expansion. -/
private theorem discriminant_hasRealQExpansion :
    HasRealQExpansionAt 1 CuspForm.discriminant := by
  have hfun : (CuspForm.discriminant : ℍ → ℂ) =
      (realDiscriminantCandidate.1 : ℍ → ℂ) := by
    funext z
    have hE₄ : realE₄Cube.1 z = ModularForm.E₄ z ^ 3 := by
      change (ModularForm.E₄ z * ModularForm.E₄ z) * ModularForm.E₄ z = _
      ring
    have hE₆ : realE₆Sq.1 z = ModularForm.E₆ z ^ 2 := by
      change ModularForm.E₆ z * ModularForm.E₆ z = _
      ring
    have hcandidate : realDiscriminantCandidate.1 z =
        ((1 / 1728 : ℝ) : ℂ) * (ModularForm.E₄ z ^ 3 - ModularForm.E₆ z ^ 2) := by
      change ((1 / 1728 : ℝ) : ℂ) * (realE₄Cube.1 z - realE₆Sq.1 z) = _
      rw [hE₄, hE₆]
    change ModularForm.discriminant z = _
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    rw [hcandidate]
    push_cast
    ring
  intro n
  rw [hfun]
  exact realDiscriminantCandidate.property n

/-- The discriminant, bundled in the real cusp-form subspace. -/
private noncomputable def realDiscriminant : RealCuspForm 12 :=
  ⟨CuspForm.discriminant, discriminant_hasRealQExpansion⟩

private theorem realDiscriminant_ne_zero : realDiscriminant ≠ 0 := by
  intro hzero
  have hcusp : CuspForm.discriminant = 0 := congrArg Subtype.val hzero
  have hvalue := congrArg (fun f : CuspForm 𝒮ℒ 12 ↦ f I) hcusp
  exact ModularForm.discriminant_ne_zero I (by simpa using hvalue)

/-- Every admissible weight at least twelve contains a nonzero coefficientwise-real cusp form.
For weight twelve this is `Δ`; in higher weights it is `Δ E_(k-12)`. -/
private theorem exists_nonzero_realCusp_of_twelve_le (k : ℕ) (hk4 : k % 4 = 0)
    (hk12 : 12 ≤ k) : ∃ g : RealCuspForm (k : ℤ), g ≠ 0 := by
  by_cases hk : k = 12
  · subst k
    exact ⟨realDiscriminant, realDiscriminant_ne_zero⟩
  · have hkgt : 12 < k := by omega
    have hjpos : 0 < k - 12 := Nat.sub_pos_of_lt hkgt
    have hj4 : (k - 12) % 4 = 0 := by omega
    let e := EisensteinDecomposition.eisenstein (k - 12) hjpos hj4
    let g0 := realCuspMul realDiscriminant e
    have hweight : (12 : ℤ) + (k - 12 : ℕ) = (k : ℤ) := by omega
    let g : RealCuspForm (k : ℤ) := realCuspMcast hweight g0
    refine ⟨g, ?_⟩
    have hDeltaModular :
        CuspForm.toModularFormₗ (realDiscriminant : CuspForm 𝒮ℒ 12) ≠ 0 := by
      exact fun h ↦ realDiscriminant_ne_zero
        (Subtype.ext (CuspForm.toModularFormₗ_injective h))
    have hE : e.1 ≠ 0 := by
      exact EisensteinSeries.E_ne_zero
        (AdmissibleWeight.three_le hjpos hj4) (AdmissibleWeight.even hj4)
    have hproduct :
        (CuspForm.toModularFormₗ (realDiscriminant : CuspForm 𝒮ℒ 12)).mul e.1 ≠ 0 :=
      ModularForm.mul_ne_zero ⟨1, one_mem_strictPeriods_SL, one_pos⟩ hDeltaModular hE
    intro hg
    apply hproduct
    have hcusp : g0.1 = 0 := by
      have hmcast : (realCuspMcast hweight g0).1 = 0 := by
        simpa [g] using congrArg Subtype.val hg
      ext z
      have hvalue := congrArg (fun f : CuspForm 𝒮ℒ (k : ℤ) ↦ f z) hmcast
      change g0.1 z = 0 at hvalue
      exact hvalue
    have hmodular := congrArg CuspForm.toModularFormₗ hcusp
    calc
      (CuspForm.toModularFormₗ (realDiscriminant : CuspForm 𝒮ℒ 12)).mul e.1 =
          CuspForm.toModularFormₗ
            ((realDiscriminant : CuspForm 𝒮ℒ 12).mulModularForm e.1) := by
            ext z
            rfl
      _ = 0 := by simpa [g0, realCuspMul] using hmodular

/-- The positive coefficients through the inclusive endpoint `N` detect global nonnegativity
for normalized real level-one modular forms of weight `k`. -/
def IsNonnegativityBound (k N : ℕ) : Prop :=
  ∀ f : NormalizedRealModularForm (k : ℤ),
    (∀ n, 1 ≤ n → n ≤ N → 0 ≤ NormalizedRealModularForm.coeff f n) →
      ∀ n, 0 ≤ NormalizedRealModularForm.coeff f n

/-- Once an initial endpoint detects nonnegativity, every larger endpoint does as well. -/
theorem isNonnegativityBound_mono {k N M : ℕ} (hNM : N ≤ M)
    (hN : IsNonnegativityBound k N) : IsNonnegativityBound k M := by
  intro f hM
  exact hN f fun n hnpos hnN ↦ hM n hnpos (hnN.trans hNM)

private theorem exists_positive_bound (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    ∃ N : ℕ, 0 < N ∧ IsNonnegativityBound k N := by
  obtain ⟨N, hN⟩ :=
    FiniteDetermination.exists_nonnegativity_bound_levelOne k hkpos hk4
  exact ⟨N + 1, Nat.zero_lt_succ N,
    isNonnegativityBound_mono (Nat.le_succ N) hN⟩

/-- `A(k)` is the least positive inclusive endpoint which detects global coefficientwise
nonnegativity when `k` is a positive multiple of four.  It is set to one outside that domain, so
the public definition is an ordinary function of the weight. -/
noncomputable def A (k : ℕ) : ℕ := by
  classical
  exact if h : 0 < k ∧ k % 4 = 0 then
    Nat.find (exists_positive_bound k h.1 h.2)
  else 1

theorem A_spec (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    0 < A k ∧ IsNonnegativityBound k (A k) := by
  classical
  rw [A, dite_eq_left ⟨hkpos, hk4⟩]
  exact Nat.find_spec (exists_positive_bound k hkpos hk4)

/-- The selected convention forces every `A(k)` to be positive, including weights whose
normalized affine slice contains no form with a negative coefficient. -/
theorem A_pos (k : ℕ) : 0 < A k := by
  classical
  rw [A]
  split
  · rename_i h
    exact (Nat.find_spec (exists_positive_bound k h.1 h.2)).1
  · norm_num

/-- Coefficients through `q^(A(k))` detect global nonnegativity. -/
theorem A_detects_nonnegativity (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0) :
    IsNonnegativityBound k (A k) :=
  (A_spec k hkpos hk4).2

/-- Minimality of `A(k)` among positive nonnegativity bounds. -/
theorem A_le_of_pos_of_isNonnegativityBound (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) {N : ℕ} (hNpos : 0 < N) (hN : IsNonnegativityBound k N) :
    A k ≤ N := by
  classical
  rw [A, dite_eq_left ⟨hkpos, hk4⟩]
  exact Nat.find_min' (exists_positive_bound k hkpos hk4) ⟨hNpos, hN⟩

/-- No smaller positive endpoint detects nonnegativity. -/
theorem not_isNonnegativityBound_of_lt_A (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) {N : ℕ} (hNpos : 0 < N) (hNA : N < A k) :
    ¬ IsNonnegativityBound k N := by
  intro hN
  exact (Nat.not_le_of_lt hNA)
    (A_le_of_pos_of_isNonnegativityBound k hkpos hk4 hNpos hN)

/-- Complete specification of the positive endpoints which detect nonnegativity. -/
theorem isNonnegativityBound_iff_A_le (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) {N : ℕ} (hNpos : 0 < N) :
    IsNonnegativityBound k N ↔ A k ≤ N := by
  constructor
  · exact A_le_of_pos_of_isNonnegativityBound k hkpos hk4 hNpos
  · intro hAN
    exact isNonnegativityBound_mono hAN
      (A_detects_nonnegativity k hkpos hk4)

/-- A coefficient is first negative at `n` when it is negative there and every earlier
coefficient is nonnegative. -/
def FirstNegativeAt {k : ℤ} (f : RealModularForm k) (n : ℕ) : Prop :=
  RealModularForm.coeff f n < 0 ∧
    ∀ m, m < n → 0 ≤ RealModularForm.coeff f m

/-- Specialized spelling for normalized real modular forms. -/
def NormalizedFirstNegativeAt {k : ℤ} (f : NormalizedRealModularForm k) (n : ℕ) : Prop :=
  FirstNegativeAt f.1 n

theorem exists_firstNegativeAt {k : ℤ} (f : RealModularForm k)
    (hnegative : ∃ n, RealModularForm.coeff f n < 0) :
    ∃ n, FirstNegativeAt f n := by
  let n := Nat.find hnegative
  refine ⟨n, Nat.find_spec hnegative, ?_⟩
  intro m hmn
  exact le_of_not_gt (Nat.find_min hnegative hmn)

theorem firstNegativeAt_unique {k : ℤ} {f : RealModularForm k} {m n : ℕ}
    (hm : FirstNegativeAt f m) (hn : FirstNegativeAt f n) : m = n := by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · exact False.elim ((not_lt_of_ge (hn.2 m hmn)) hm.1)
  · exact hmn
  · exact False.elim ((not_lt_of_ge (hm.2 n hnm)) hn.1)

/-- A normalized form cannot have its first negative coefficient at index zero. -/
theorem normalized_firstNegativeAt_pos {k : ℤ} {f : NormalizedRealModularForm k} {n : ℕ}
    (hn : NormalizedFirstNegativeAt f n) : 0 < n := by
  by_contra hn0
  have : n = 0 := Nat.eq_zero_of_not_pos hn0
  subst n
  have hf0 : RealModularForm.coeff f.1 0 = 1 := f.property
  change RealModularForm.coeff f.1 0 < 0 ∧ _ at hn
  rw [hf0] at hn
  norm_num at hn

/-- Every first negative index of a normalized form is at most `A(k)`. -/
theorem normalized_firstNegativeAt_le_A (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) {f : NormalizedRealModularForm (k : ℤ)} {n : ℕ}
    (hn : NormalizedFirstNegativeAt f n) : n ≤ A k := by
  by_contra hnle
  have hAn : A k < n := Nat.lt_of_not_ge hnle
  have hinitial : ∀ m, 1 ≤ m → m ≤ A k →
      0 ≤ NormalizedRealModularForm.coeff f m := by
    intro m _ hmA
    exact hn.2 m (hmA.trans_lt hAn)
  have hall := A_detects_nonnegativity k hkpos hk4 f hinitial
  exact (not_lt_of_ge (hall n)) hn.1

/-- There is a normalized form of weight `k` having a negative coefficient. -/
def HasNegativeNormalizedForm (k : ℕ) : Prop :=
  ∃ f : NormalizedRealModularForm (k : ℤ), ∃ n, NormalizedRealModularForm.coeff f n < 0

/-- The normalized counterexample family is nonempty in every admissible weight at least twelve.
The construction perturbs the normalized Eisenstein series in a nonzero real cusp direction
whose negative coefficient is supplied by the analytic sign-change theorem. -/
theorem hasNegativeNormalizedForm_of_twelve_le (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (hk12 : 12 ≤ k) : HasNegativeNormalizedForm k := by
  obtain ⟨g, hg⟩ := exists_nonzero_realCusp_of_twelve_le k hk4 hk12
  have hkzpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hkpos
  obtain ⟨n, hnpos, hnneg⟩ := RealCuspForm.exists_coeff_neg hkzpos g hg
  let en : ℝ := EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n
  let bn : ℝ := RealCuspForm.coeff g n
  let t : ℝ := (en + 1) / (-bn)
  let F : NormalizedRealModularForm (k : ℤ) := by
    refine ⟨EisensteinDecomposition.eisenstein k hkpos hk4 +
      t • RealCuspForm.toRealModularForm g, ?_⟩
    change RealModularForm.coeffLinear 0
      (EisensteinDecomposition.eisenstein k hkpos hk4 +
        t • RealCuspForm.toRealModularForm g) = 1
    rw [map_add, map_smul]
    change RealModularForm.coeff (EisensteinDecomposition.eisenstein k hkpos hk4) 0 +
      t * RealModularForm.coeff (RealCuspForm.toRealModularForm g) 0 = 1
    rw [EisensteinDecomposition.eisenstein_coeff_zero,
      RealCuspForm.coeff_toRealModularForm, RealCuspForm.coeff_zero]
    ring
  refine ⟨F, n, ?_⟩
  change RealModularForm.coeff
    (EisensteinDecomposition.eisenstein k hkpos hk4 +
      t • RealCuspForm.toRealModularForm g) n < 0
  change RealModularForm.coeffLinear n
    (EisensteinDecomposition.eisenstein k hkpos hk4 +
      t • RealCuspForm.toRealModularForm g) < 0
  rw [map_add, map_smul]
  change en + t * bn < 0
  have hbn : bn < 0 := hnneg
  have hcancel : (-bn)⁻¹ * bn = -1 := by
    rw [inv_neg, neg_mul, inv_mul_cancel₀ (ne_of_lt hbn)]
  have hscale : en + t * bn = -1 := by
    dsimp [t]
    rw [div_eq_mul_inv]
    calc
      en + (en + 1) * (-bn)⁻¹ * bn =
          en + (en + 1) * ((-bn)⁻¹ * bn) := by ring
      _ = -1 := by rw [hcancel]; ring
  rw [hscale]
  norm_num

/-- The set of indices which occur as the first negative index of a normalized form. -/
def normalizedFirstNegativeIndices (k : ℕ) : Set ℕ :=
  {n | ∃ f : NormalizedRealModularForm (k : ℤ), NormalizedFirstNegativeAt f n}

/-- In the nontrivial range, minimality of `A(k)` produces a normalized form whose first
negative coefficient occurs exactly at `A(k)`. -/
theorem exists_normalized_firstNegativeAt_A (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (hnontrivial : HasNegativeNormalizedForm k) :
    ∃ f : NormalizedRealModularForm (k : ℤ),
      NormalizedFirstNegativeAt f (A k) := by
  let a := A k
  by_cases haone : a = 1
  · obtain ⟨f, n, hn⟩ := hnontrivial
    obtain ⟨m, hm⟩ := exists_firstNegativeAt f.1 ⟨n, hn⟩
    have hmnorm : NormalizedFirstNegativeAt f m := hm
    have hmpos : 0 < m := normalized_firstNegativeAt_pos hmnorm
    have hmle : m ≤ a := by
      exact normalized_firstNegativeAt_le_A k hkpos hk4 hmnorm
    have hma : m = a := by omega
    exact ⟨f, by simpa [a, hma] using hmnorm⟩
  · have hapos : 0 < a := A_pos k
    have haone_lt : 1 < a := by omega
    have hpredpos : 0 < a - 1 := by omega
    have hpredlt : a - 1 < A k := by
      change a - 1 < a
      omega
    have hnot := not_isNonnegativityBound_of_lt_A k hkpos hk4 hpredpos hpredlt
    simp only [IsNonnegativityBound, not_forall, not_le] at hnot
    obtain ⟨f, hinitial, n, hnneg⟩ := hnot
    have haneg : NormalizedRealModularForm.coeff f a < 0 := by
      apply lt_of_not_ge
      intro hanonneg
      have hall := A_detects_nonnegativity k hkpos hk4 f (by
        intro m hmpos hmA
        by_cases hma : m = a
        · simpa [hma] using hanonneg
        · exact hinitial m hmpos (by omega))
      exact (not_lt_of_ge (hall n)) hnneg
    refine ⟨f, haneg, ?_⟩
    intro m hma
    by_cases hm0 : m = 0
    · subst m
      rw [f.property]
      norm_num
    · exact hinitial m (Nat.one_le_iff_ne_zero.mpr hm0) (by omega)

/-- The paper's maximum characterization: in the nontrivial range, `A(k)` is the greatest
index which occurs as the first negative coefficient of a normalized form. -/
theorem A_isGreatest_normalizedFirstNegativeIndices (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (hnontrivial : HasNegativeNormalizedForm k) :
    IsGreatest (normalizedFirstNegativeIndices k) (A k) := by
  constructor
  · exact exists_normalized_firstNegativeAt_A k hkpos hk4 hnontrivial
  · rintro n ⟨f, hn⟩
    exact normalized_firstNegativeAt_le_A k hkpos hk4 hn

/-- In every admissible weight at least twelve, a normalized form has its first negative
coefficient exactly at `A(k)`. -/
theorem exists_normalized_firstNegativeAt_A_of_twelve_le (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (hk12 : 12 ≤ k) :
    ∃ f : NormalizedRealModularForm (k : ℤ),
      NormalizedFirstNegativeAt f (A k) :=
  exists_normalized_firstNegativeAt_A k hkpos hk4
    (hasNegativeNormalizedForm_of_twelve_le k hkpos hk4 hk12)

/-- Unconditional maximum characterization in the nontrivial admissible range `12 ≤ k`. -/
theorem A_isGreatest_normalizedFirstNegativeIndices_of_twelve_le (k : ℕ)
    (hkpos : 0 < k) (hk4 : k % 4 = 0) (hk12 : 12 ≤ k) :
    IsGreatest (normalizedFirstNegativeIndices k) (A k) :=
  A_isGreatest_normalizedFirstNegativeIndices k hkpos hk4
    (hasNegativeNormalizedForm_of_twelve_le k hkpos hk4 hk12)

/-- If the normalized counterexample family is empty, the selected positive convention gives
`A(k) = 1`. -/
theorem A_eq_one_of_no_negative (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    (hempty : ¬ HasNegativeNormalizedForm k) : A k = 1 := by
  have hone : IsNonnegativityBound k 1 := by
    intro f _ n
    exact le_of_not_gt fun hn ↦ hempty ⟨f, n, hn⟩
  have hAle : A k ≤ 1 :=
    A_le_of_pos_of_isNonnegativityBound k hkpos hk4 one_pos hone
  exact Nat.le_antisymm hAle (A_pos k)

@[simp] theorem coeff_add {k : ℤ} (f g : RealModularForm k) (n : ℕ) :
    RealModularForm.coeff (f + g) n =
      RealModularForm.coeff f n + RealModularForm.coeff g n := by
  change RealModularForm.coeffLinear n (f + g) = _
  rw [map_add]
  rfl

@[simp] theorem coeff_smul {k : ℤ} (r : ℝ) (f : RealModularForm k) (n : ℕ) :
    RealModularForm.coeff (r • f) n = r * RealModularForm.coeff f n := by
  change RealModularForm.coeffLinear n (r • f) = _
  rw [map_smul]
  rfl

/-- The cutoff `A(k)` also detects global nonnegativity for arbitrary real modular forms,
provided coefficient zero is included among the tested coefficients.  The proof treats positive,
zero, and negative constant terms separately. -/
theorem realModularForm_nonnegative_of_nonnegative_up_to_A (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (f : RealModularForm (k : ℤ))
    (hinitial : ∀ n, n ≤ A k → 0 ≤ RealModularForm.coeff f n) :
    ∀ n, 0 ≤ RealModularForm.coeff f n := by
  rcases lt_trichotomy (RealModularForm.coeff f 0) 0 with hcneg | hczero | hcpos
  · exact False.elim ((not_lt_of_ge (hinitial 0 (Nat.zero_le _))) hcneg)
  · intro n
    by_contra hnnonneg
    have hnneg : RealModularForm.coeff f n < 0 := lt_of_not_ge hnnonneg
    have hnpos : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      exact (not_lt_of_ge hczero.ge) hnneg
    let en : ℝ := EisensteinDecomposition.eisensteinCoeff k hkpos hk4 n
    let an : ℝ := RealModularForm.coeff f n
    let t : ℝ := (en + 1) / (-an)
    have henpos : 0 < en :=
      EisensteinPositivity.eisensteinCoeff_pos k hkpos hk4 n hnpos
    have hanneg : an < 0 := hnneg
    have hdenpos : 0 < -an := neg_pos.mpr hanneg
    have htpos : 0 < t := by
      exact div_pos (by positivity) hdenpos
    let F : NormalizedRealModularForm (k : ℤ) := by
      refine ⟨EisensteinDecomposition.eisenstein k hkpos hk4 + t • f, ?_⟩
      rw [coeff_add, coeff_smul,
        EisensteinDecomposition.eisenstein_coeff_zero, hczero]
      ring
    have hFcoeff (m : ℕ) :
        NormalizedRealModularForm.coeff F m =
          EisensteinDecomposition.eisensteinCoeff k hkpos hk4 m +
            t * RealModularForm.coeff f m := by
      change RealModularForm.coeff
        (EisensteinDecomposition.eisenstein k hkpos hk4 + t • f) m = _
      rw [coeff_add, coeff_smul]
      rfl
    have hFinitial : ∀ m, 1 ≤ m → m ≤ A k →
        0 ≤ NormalizedRealModularForm.coeff F m := by
      intro m hmpos hmA
      rw [hFcoeff]
      exact add_nonneg
        (EisensteinPositivity.eisensteinCoeff_pos k hkpos hk4 m hmpos).le
        (mul_nonneg htpos.le (hinitial m hmA))
    have hFall := A_detects_nonnegativity k hkpos hk4 F hFinitial
    have hscale : en + t * an = -1 := by
      dsimp [t]
      rw [div_eq_mul_inv]
      have hnegcancel : (-an)⁻¹ * an = -1 := by
        rw [inv_neg, neg_mul, inv_mul_cancel₀ (ne_of_lt hanneg)]
      calc
        en + (en + 1) * (-an)⁻¹ * an =
            en + (en + 1) * ((-an)⁻¹ * an) := by ring
        _ = -1 := by rw [hnegcancel]; ring
    have hFnneg : NormalizedRealModularForm.coeff F n < 0 := by
      rw [hFcoeff]
      change en + t * an < 0
      rw [hscale]
      norm_num
    exact (not_lt_of_ge (hFall n)) hFnneg
  · let c : ℝ := RealModularForm.coeff f 0
    let F : NormalizedRealModularForm (k : ℤ) := by
      refine ⟨c⁻¹ • f, ?_⟩
      rw [coeff_smul]
      change c⁻¹ * c = 1
      exact inv_mul_cancel₀ (ne_of_gt hcpos)
    have hFcoeff (n : ℕ) :
        NormalizedRealModularForm.coeff F n = c⁻¹ * RealModularForm.coeff f n := by
      change RealModularForm.coeff (c⁻¹ • f) n = _
      rw [coeff_smul]
    have hFinitial : ∀ n, 1 ≤ n → n ≤ A k →
        0 ≤ NormalizedRealModularForm.coeff F n := by
      intro n _ hnA
      rw [hFcoeff]
      exact mul_nonneg (inv_pos.mpr hcpos).le (hinitial n hnA)
    have hFall := A_detects_nonnegativity k hkpos hk4 F hFinitial
    intro n
    have hprod := hFall n
    rw [hFcoeff] at hprod
    exact nonneg_of_mul_nonneg_right hprod (inv_pos.mpr hcpos)

/-- Every first negative index of an arbitrary real modular form is at most `A(k)`. -/
theorem firstNegativeAt_le_A (k : ℕ) (hkpos : 0 < k) (hk4 : k % 4 = 0)
    {f : RealModularForm (k : ℤ)} {n : ℕ} (hn : FirstNegativeAt f n) :
    n ≤ A k := by
  by_contra hnle
  have hAn : A k < n := Nat.lt_of_not_ge hnle
  have hinitial : ∀ m, m ≤ A k →
      0 ≤ RealModularForm.coeff f m := by
    intro m hmA
    exact hn.2 m (hmA.trans_lt hAn)
  have hall := realModularForm_nonnegative_of_nonnegative_up_to_A
    k hkpos hk4 f hinitial
  exact (not_lt_of_ge (hall n)) hn.1

/-- The set used in the paper's maximum definition: all first negative indices of arbitrary real
level-one modular forms of weight `k`. -/
def firstNegativeIndices (k : ℕ) : Set ℕ :=
  {n | ∃ f : RealModularForm (k : ℤ), FirstNegativeAt f n}

/-- In the nontrivial normalized range, `A(k)` is also the greatest first negative index among
all real modular forms, matching the paper's maximum characterization. -/
theorem A_isGreatest_firstNegativeIndices (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (hnontrivial : HasNegativeNormalizedForm k) :
    IsGreatest (firstNegativeIndices k) (A k) := by
  constructor
  · obtain ⟨f, hf⟩ := exists_normalized_firstNegativeAt_A k hkpos hk4 hnontrivial
    exact ⟨f.1, hf⟩
  · rintro n ⟨f, hn⟩
    exact firstNegativeAt_le_A k hkpos hk4 hn

/-- For every admissible `k ≥ 12`, `A(k)` is the greatest first negative index among all
real modular forms of weight `k`. -/
theorem A_isGreatest_firstNegativeIndices_of_twelve_le (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (hk12 : 12 ≤ k) :
    IsGreatest (firstNegativeIndices k) (A k) :=
  A_isGreatest_firstNegativeIndices k hkpos hk4
    (hasNegativeNormalizedForm_of_twelve_le k hkpos hk4 hk12)

/-- Below weight twelve the normalized affine slice consists only of the Eisenstein series, so
all of its coefficients are nonnegative. -/
theorem normalized_coeff_nonneg_of_lt_twelve (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (hk12 : k < 12)
    (f : NormalizedRealModularForm (k : ℤ)) (n : ℕ) :
    0 ≤ NormalizedRealModularForm.coeff f n := by
  have hkz12 : (k : ℤ) < 12 := by exact_mod_cast hk12
  have hcuspComplex :
      (EisensteinDecomposition.cuspPart k hkpos hk4 f : CuspForm 𝒮ℒ (k : ℤ)) = 0 :=
    (rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve hkz12)) _
  have hcusp : EisensteinDecomposition.cuspPart k hkpos hk4 f = 0 := by
    apply Subtype.ext
    exact hcuspComplex
  have hcoord : EisensteinDecomposition.cuspCoordinates k hkpos hk4 f = 0 := by
    apply (RealCuspForm.Coordinates.toForm (k : ℤ)).injective
    rw [EisensteinDecomposition.coordinates_to_cuspPart, hcusp, map_zero]
  rw [EisensteinDecomposition.coeff_eq_eisenstein_add_coordinate, hcoord, map_zero,
    add_zero]
  by_cases hn0 : n = 0
  · subst n
    change 0 ≤ RealModularForm.coeff
      (EisensteinDecomposition.eisenstein k hkpos hk4) 0
    simp
  · exact (EisensteinPositivity.eisensteinCoeff_pos k hkpos hk4 n
      (Nat.pos_of_ne_zero hn0)).le

theorem no_negativeNormalizedForm_of_lt_twelve (k : ℕ) (hkpos : 0 < k)
    (hk4 : k % 4 = 0) (hk12 : k < 12) :
    ¬ HasNegativeNormalizedForm k := by
  rintro ⟨f, n, hn⟩
  exact (not_lt_of_ge (normalized_coeff_nonneg_of_lt_twelve k hkpos hk4 hk12 f n)) hn

/-- Selected empty-family convention in weight four. -/
theorem A_four : A 4 = 1 := by
  exact A_eq_one_of_no_negative 4 (by norm_num) (by norm_num)
    (no_negativeNormalizedForm_of_lt_twelve 4 (by norm_num) (by norm_num) (by norm_num))

/-- Selected empty-family convention in weight eight. -/
theorem A_eight : A 8 = 1 := by
  exact A_eq_one_of_no_negative 8 (by norm_num) (by norm_num)
    (no_negativeNormalizedForm_of_lt_twelve 8 (by norm_num) (by norm_num) (by norm_num))

end NonnegativityBound

end Section4.RealForms
