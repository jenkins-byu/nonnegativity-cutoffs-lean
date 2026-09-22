import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Lattice

/-!
# A finite-half-space theorem

This file isolates the compactness argument needed in Section 4 from modular forms.
It treats an arbitrary sequence of affine half-spaces in a finite-dimensional real normed
space.  A directional sign obstruction supplies a bounded finite subintersection; an eventual
local-validity hypothesis then reduces the full countable intersection to finitely many of the
half-spaces.
-/

open Filter Metric Set
open scoped Topology

namespace Section4.FiniteHalfspace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The affine half-space cut out by the inequality `0 ≤ e n + b n v`. -/
def halfspace (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ) (n : ℕ) : Set V :=
  {v | 0 ≤ e n + b n v}

/-- The intersection indexed by a finite set of natural numbers. -/
def finiteIntersection (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ) (I : Finset ℕ) : Set V :=
  {v | ∀ n ∈ I, v ∈ halfspace e b n}

/-- The full countable intersection. -/
def fullIntersection (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ) : Set V :=
  {v | ∀ n, v ∈ halfspace e b n}

/-- Every fixed closed ball is eventually contained in the indexed affine half-spaces. -/
def EventuallyContainsClosedBalls (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ᶠ n in atTop, closedBall (0 : V) R ⊆ halfspace e b n

@[simp] theorem mem_halfspace {e : ℕ → ℝ} {b : ℕ → V →L[ℝ] ℝ} {n : ℕ} {v : V} :
    v ∈ halfspace e b n ↔ 0 ≤ e n + b n v :=
  Iff.rfl

@[simp] theorem mem_finiteIntersection {e : ℕ → ℝ} {b : ℕ → V →L[ℝ] ℝ}
    {I : Finset ℕ} {v : V} :
    v ∈ finiteIntersection e b I ↔ ∀ n ∈ I, v ∈ halfspace e b n :=
  Iff.rfl

@[simp] theorem mem_fullIntersection {e : ℕ → ℝ} {b : ℕ → V →L[ℝ] ℝ} {v : V} :
    v ∈ fullIntersection e b ↔ ∀ n, v ∈ halfspace e b n :=
  Iff.rfl

theorem fullIntersection_subset_finiteIntersection (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (I : Finset ℕ) :
    fullIntersection e b ⊆ finiteIntersection e b I := by
  intro v hv n hn
  exact hv n

theorem finiteIntersection_anti (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    {I J : Finset ℕ} (hIJ : I ⊆ J) :
    finiteIntersection e b J ⊆ finiteIntersection e b I := by
  intro v hv n hn
  exact hv n (hIJ hn)

theorem isClosed_halfspace (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ) (n : ℕ) :
    IsClosed (halfspace e b n) := by
  exact isClosed_le continuous_const (continuous_const.add (b n).continuous)

theorem convex_halfspace (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ) (n : ℕ) :
    Convex ℝ (halfspace e b n) := by
  intro x hx y hy a c ha hc hac
  simp only [mem_halfspace] at hx hy ⊢
  rw [map_add, map_smul, map_smul]
  calc
    0 ≤ a * (e n + b n x) + c * (e n + b n y) :=
      add_nonneg (mul_nonneg ha hx) (mul_nonneg hc hy)
    _ = e n + (a * b n x + c * b n y) := by
      linear_combination (e n) * hac

theorem isClosed_finiteIntersection (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (I : Finset ℕ) :
    IsClosed (finiteIntersection e b I) := by
  rw [show finiteIntersection e b I = ⋂ n : {n // n ∈ I}, halfspace e b n by
    ext v
    simp [finiteIntersection]]
  exact isClosed_iInter fun n ↦ isClosed_halfspace e b n

theorem convex_finiteIntersection (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (I : Finset ℕ) :
    Convex ℝ (finiteIntersection e b I) := by
  rw [show finiteIntersection e b I = ⋂ n : {n // n ∈ I}, halfspace e b n by
    ext v
    simp [finiteIntersection]]
  exact convex_iInter fun n ↦ convex_halfspace e b n

theorem isClosed_fullIntersection (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ) :
    IsClosed (fullIntersection e b) := by
  rw [show fullIntersection e b = ⋂ n, halfspace e b n by
    ext v
    simp [fullIntersection]]
  exact isClosed_iInter fun n ↦ isClosed_halfspace e b n

theorem convex_fullIntersection (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ) :
    Convex ℝ (fullIntersection e b) := by
  rw [show fullIntersection e b = ⋂ n, halfspace e b n by
    ext v
    simp [fullIntersection]]
  exact convex_iInter fun n ↦ convex_halfspace e b n

/-- If the linear parts of the inequalities detect every nonzero direction negatively, then
some finite collection of the affine half-spaces already has bounded intersection.

The proof covers the unit sphere by the open sets on which one of the functionals is negative,
extracts a finite subcover, and uses compactness once more to obtain a uniform negative margin.
The argument also covers zero-dimensional spaces: in that case the unit sphere is empty and the
intersection is automatically contained in every sufficiently large ball. -/
theorem exists_bounded_finiteIntersection [FiniteDimensional ℝ V]
    (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (hdetect : ∀ v : V, v ≠ 0 → ∃ n, b n v < 0) :
    ∃ I : Finset ℕ, Bornology.IsBounded (finiteIntersection e b I) := by
  let U : ℕ → Set V := fun n ↦ {v | b n v < 0}
  have hUopen : ∀ n, IsOpen (U n) := fun n ↦
    isOpen_lt (b n).continuous continuous_const
  have hcover : sphere (0 : V) 1 ⊆ ⋃ n, U n := by
    intro v hv
    have hv0 : v ≠ 0 := by
      intro h
      subst v
      norm_num [mem_sphere] at hv
    obtain ⟨n, hn⟩ := hdetect v hv0
    exact mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨I, hI⟩ :=
    (isCompact_sphere (0 : V) 1).elim_finite_subcover U hUopen hcover
  let J : Finset ℕ := insert 0 I
  have hJ : J.Nonempty := ⟨0, Finset.mem_insert_self 0 I⟩
  let m : V → ℝ := fun v ↦ J.inf' hJ fun n ↦ b n v
  have hm_cont : Continuous m := by
    exact Continuous.finset_inf'_apply hJ fun n _ ↦ (b n).continuous
  have hm_neg : ∀ v ∈ sphere (0 : V) 1, m v < 0 := by
    intro v hv
    rcases mem_iUnion.1 (hI hv) with ⟨n, hn⟩
    rcases mem_iUnion.1 hn with ⟨hnI, hnv⟩
    exact lt_of_le_of_lt (Finset.inf'_le (fun i ↦ b i v) (Finset.mem_insert_of_mem hnI)) hnv
  obtain ⟨δ, hδ, hmargin⟩ :=
    (isCompact_sphere (0 : V) 1).exists_forall_le'
      hm_cont.neg.continuousOn (fun v hv ↦ neg_pos.2 (hm_neg v hv))
  let C : ℝ := ∑ n ∈ J, |e n|
  have hC : 0 ≤ C := by
    exact Finset.sum_nonneg fun n _ ↦ abs_nonneg (e n)
  refine ⟨J, (Metric.isBounded_iff_subset_closedBall (0 : V)).2 ⟨C / δ, ?_⟩⟩
  intro v hv
  rw [mem_closedBall, dist_zero_right]
  by_cases hv0 : v = 0
  · subst v
    simpa using div_nonneg hC hδ.le
  · have hvnorm : 0 < ‖v‖ := norm_pos_iff.2 hv0
    let u : V := ‖v‖⁻¹ • v
    have hunorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hvnorm.ne']
    have hu_sphere : u ∈ sphere (0 : V) 1 := by
      simpa [mem_sphere, dist_zero_right] using hunorm
    have hδu : δ ≤ -m u := hmargin u hu_sphere
    obtain ⟨i, hiJ, hmi⟩ := J.exists_mem_eq_inf' hJ fun n ↦ b n u
    have hbiu : b i u ≤ -δ := by
      rw [← hmi]
      linarith
    have hv_eq : ‖v‖ • u = v := by
      simp [u, smul_smul, hvnorm.ne']
    have hscale : b i v = ‖v‖ * b i u := by
      calc
        b i v = b i (‖v‖ • u) := congrArg (b i) hv_eq.symm
        _ = ‖v‖ • b i u := map_smul (b i) ‖v‖ u
        _ = ‖v‖ * b i u := by rw [smul_eq_mul]
    have hbiv : b i v ≤ -(‖v‖ * δ) := by
      rw [hscale]
      nlinarith [mul_le_mul_of_nonneg_left hbiu hvnorm.le]
    have haffine : 0 ≤ e i + b i v := hv i hiJ
    have heiC : |e i| ≤ C := by
      exact Finset.single_le_sum (fun n _ ↦ abs_nonneg (e n)) hiJ
    apply (le_div_iff₀ hδ).2
    nlinarith [le_abs_self (e i)]

/-- Under directional detection, the full intersection is bounded, before any tail hypothesis
is imposed. -/
theorem isBounded_fullIntersection_of_detects [FiniteDimensional ℝ V]
    (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (hdetect : ∀ v : V, v ≠ 0 → ∃ n, b n v < 0) :
    Bornology.IsBounded (fullIntersection e b) := by
  obtain ⟨I, hI⟩ := exists_bounded_finiteIntersection e b hdetect
  exact hI.subset (fullIntersection_subset_finiteIntersection e b I)

/-- Under directional detection, the full intersection is compact. -/
theorem isCompact_fullIntersection_of_detects [FiniteDimensional ℝ V]
    (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (hdetect : ∀ v : V, v ≠ 0 → ∃ n, b n v < 0) :
    IsCompact (fullIntersection e b) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_fullIntersection e b)
    (isBounded_fullIntersection_of_detects e b hdetect)

/-- The generic finite-reduction theorem used by the planned Section 4 formalization.

The first hypothesis says that the homogeneous linear parts detect every nonzero direction by
a strict negative value.  The second says that, on every fixed bounded region, all sufficiently
late affine inequalities hold automatically.  The conclusion gives an actual finite set of
indices whose intersection is bounded and equals the full countable intersection. -/
theorem exists_finite_reduction [FiniteDimensional ℝ V]
    (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (hdetect : ∀ v : V, v ≠ 0 → ∃ n, b n v < 0)
    (htail : EventuallyContainsClosedBalls e b) :
    ∃ I : Finset ℕ,
      Bornology.IsBounded (finiteIntersection e b I) ∧
        finiteIntersection e b I = fullIntersection e b := by
  obtain ⟨B, hB⟩ := exists_bounded_finiteIntersection e b hdetect
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : V)).1 hB
  let R : ℝ := max r 0
  have hR : 0 ≤ R := le_max_right r 0
  have hBR : finiteIntersection e b B ⊆ closedBall (0 : V) R :=
    hr.trans (closedBall_subset_closedBall (le_max_left r 0))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htail R hR)
  let I : Finset ℕ := B ∪ Finset.range N
  have hBI : B ⊆ I := Finset.subset_union_left
  have hboundedI : Bornology.IsBounded (finiteIntersection e b I) :=
    hB.subset (finiteIntersection_anti e b hBI)
  refine ⟨I, hboundedI, Set.Subset.antisymm ?_ ?_⟩
  · intro v hv n
    by_cases hn : n < N
    · exact hv n (Finset.mem_union_right B (Finset.mem_range.2 hn))
    · have hvB : v ∈ finiteIntersection e b B :=
        finiteIntersection_anti e b hBI hv
      exact hN n (Nat.le_of_not_gt hn) (hBR hvB)
  · exact fullIntersection_subset_finiteIntersection e b I

/-- A version of `exists_finite_reduction` in which the finite set is replaced by an initial
segment.  This is often the form needed for a least cutoff such as the paper's `A(k)`. -/
theorem exists_initialSegment_reduction [FiniteDimensional ℝ V]
    (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (hdetect : ∀ v : V, v ≠ 0 → ∃ n, b n v < 0)
    (htail : EventuallyContainsClosedBalls e b) :
    ∃ N : ℕ,
      Bornology.IsBounded (finiteIntersection e b (Finset.range N)) ∧
        finiteIntersection e b (Finset.range N) = fullIntersection e b := by
  obtain ⟨I, hboundedI, hIfull⟩ := exists_finite_reduction e b hdetect htail
  obtain ⟨N, hIN⟩ := I.exists_nat_subset_range
  have hboundedN : Bornology.IsBounded (finiteIntersection e b (Finset.range N)) :=
    hboundedI.subset (finiteIntersection_anti e b hIN)
  refine ⟨N, hboundedN, Set.Subset.antisymm ?_ ?_⟩
  · exact (finiteIntersection_anti e b hIN).trans_eq hIfull
  · exact fullIntersection_subset_finiteIntersection e b (Finset.range N)

/-- Compactness of the finite witness furnished by the generic theorem. -/
theorem exists_compact_finite_reduction [FiniteDimensional ℝ V]
    (e : ℕ → ℝ) (b : ℕ → V →L[ℝ] ℝ)
    (hdetect : ∀ v : V, v ≠ 0 → ∃ n, b n v < 0)
    (htail : EventuallyContainsClosedBalls e b) :
    ∃ I : Finset ℕ,
      IsCompact (finiteIntersection e b I) ∧
        Convex ℝ (finiteIntersection e b I) ∧
          finiteIntersection e b I = fullIntersection e b := by
  obtain ⟨I, hboundedI, hIfull⟩ := exists_finite_reduction e b hdetect htail
  exact ⟨I,
    Metric.isCompact_of_isClosed_isBounded (isClosed_finiteIntersection e b I) hboundedI,
    convex_finiteIntersection e b I, hIfull⟩

end Section4.FiniteHalfspace
