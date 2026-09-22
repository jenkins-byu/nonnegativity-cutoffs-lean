import Mathlib.NumberTheory.LSeries.Positivity

/-!
# Positivity of analytically continued L-series

Mathlib's corresponding theorem assumes that the coefficient at index `1` is strictly positive.
For the Section 4 sign-change argument it is enough that some coefficient at a nonzero index is
strictly positive.  This file records that reusable generalization independently of modular forms.
-/

open Filter Set
open scoped ComplexOrder

namespace Section4.LSeriesPositivity

/-- Strict positivity of an L-series in its half-plane of absolute convergence only needs one
strictly positive coefficient at a nonzero index. -/
lemma positive_of_exists_pos {a : ℕ → ℂ} (ha₀ : 0 ≤ a)
    (ha_pos : ∃ n, n ≠ 0 ∧ 0 < a n) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) :
    0 < _root_.LSeries a x := by
  obtain ⟨n, hn, han⟩ := ha_pos
  rw [_root_.LSeries]
  refine Summable.tsum_pos ?_ (fun m ↦ LSeries.term_nonneg (ha₀ m) x) n
    (LSeries.term_pos hn han x)
  exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by
    simpa only [Complex.ofReal_re] using hx

/-- Analytic continuation of `positive_of_exists_pos`.  This generalizes
`LSeries.positive_of_differentiable_of_eqOn` from positivity at index `1` to positivity at an
arbitrary nonzero index. -/
lemma positive_of_differentiable_of_eqOn_of_exists_pos {a : ℕ → ℂ} (ha₀ : 0 ≤ a)
    (ha_pos : ∃ n, n ≠ 0 ∧ 0 < a n) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℝ} (hx : LSeries.abscissaOfAbsConv a ≤ x)
    (hf' : {s | x < s.re}.EqOn f (_root_.LSeries a)) (y : ℝ) :
    0 < f y := by
  have hxy : x < max x y + 1 := (le_max_left x y).trans_lt (lt_add_one _)
  have hxy' : LSeries.abscissaOfAbsConv a < max x y + 1 := hx.trans_lt <| mod_cast hxy
  have hys : (max x y + 1 : ℂ) ∈ {s | x < s.re} := by
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.one_re, hxy]
  have hfx : 0 < f (max x y + 1) := by
    simpa only [hf' hys, Complex.ofReal_add, Complex.ofReal_one] using
      positive_of_exists_pos ha₀ ha_pos hxy'
  refine hfx.trans_le <| hf.apply_le_of_iteratedDeriv_alternating (fun n _ ↦ ?_) ?_
  · have hs : IsOpen {s : ℂ | x < s.re} :=
      Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    simpa only [hf'.iteratedDeriv_of_isOpen hs n hys, Complex.ofReal_add,
      Complex.ofReal_one] using LSeries.iteratedDeriv_alternating ha₀ hxy' n
  · exact_mod_cast (le_max_right x y).trans (lt_add_one _).le

end Section4.LSeriesPositivity
