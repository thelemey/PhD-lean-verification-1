import Thesis.SymbolicLatticeMetric
import Mathlib.Data.Int.Interval
import Mathlib.Topology.MetricSpace.Lipschitz

open Set
open scoped BigOperators

noncomputable section

namespace Thesis.SymbolicLattice

private theorem geom_summable : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

private theorem summable_cutoff (k : ℕ) :
    Summable (fun n : ℕ => if k ≤ n then (1 / 2 : ℝ) ^ n else 0) := by
  apply Summable.of_nonneg_of_le _ _ geom_summable
  · intro n
    split <;> positivity
  · intro n
    split
    · exact le_rfl
    · positivity

private theorem tsum_cutoff (k : ℕ) :
    (∑' n : ℕ, if k ≤ n then (1 / 2 : ℝ) ^ n else 0) = (1 / 2 : ℝ) ^ k * 2 := by
  have hz : (∑ n ∈ Finset.range k, if k ≤ n then (1 / 2 : ℝ) ^ n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Nat.not_le_of_lt (Finset.mem_range.mp hi)]
  rw [← (summable_cutoff k).sum_add_tsum_nat_add k, hz, zero_add]
  simp only [Nat.le_add_left, if_true, pow_add]
  rw [Summable.tsum_mul_right _ geom_summable,
    tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]
  ring

/-- The weight outside the centered window ([-r,r]), exactly the
geometric tail in the proof of `propositionn1`. -/
theorem weight_tail (r : ℕ) :
    (∑' i : ℤ, if r < i.natAbs then weight i else 0) = 2 * (1 / 2 : ℝ) ^ r := by
  let f : ℤ → ℝ := fun i => if r < i.natAbs then weight i else 0
  have hpos (n : ℕ) : f (n : ℤ) = if r + 1 ≤ n then (1 / 2 : ℝ) ^ n else 0 := by
    simp only [f, weight, Int.natAbs_ofNat, Nat.succ_le_iff]
  have hneg (n : ℕ) : f (-(↑n + 1)) =
      (if r ≤ n then (1 / 2 : ℝ) ^ n else 0) * (1 / 2) := by
    have hi : (-(↑n + 1) : ℤ).natAbs = n + 1 := by omega
    simp only [f, weight, hi, Nat.lt_succ_iff, pow_succ]
    split <;> simp
  have hsp : Summable (fun n : ℕ => f n) := by simp_rw [hpos]; exact summable_cutoff _
  have hsn : Summable (fun n : ℕ => f (-(↑n + 1))) := by
    simp_rw [hneg]
    exact (summable_cutoff r).mul_right _
  change (∑' i, f i) = _
  rw [tsum_of_nat_of_neg_add_one hsp hsn]
  simp_rw [hpos, hneg]
  rw [Summable.tsum_mul_right _ (summable_cutoff r), tsum_cutoff (r + 1),
    tsum_cutoff r, pow_succ]
  ring

section Cylinders

variable {A E : Type*} [NormedAddCommGroup E]

/-- Agreement on the centered window bounds the distance by exactly the
upper estimate (2^{1-r}) used in the thesis. -/
theorem distance_le_of_agree (ζ : A → E) (x y : ℤ → A) (r : ℕ)
    (h : ∀ i, i.natAbs ≤ r → x i = y i) :
    distance ζ x y ≤ 2 * (1 / 2 : ℝ) ^ r := by
  have hs : Summable (fun i : ℤ => if r < i.natAbs then weight i else 0) := by
    apply Summable.of_nonneg_of_le _ _ summable_weight
    · intro i
      split <;> first | exact (weight_pos i).le | exact le_rfl
    · intro i
      split <;> first | exact le_rfl | exact (weight_pos i).le
  rw [← weight_tail r, distance]
  apply Summable.tsum_le_tsum _ (summable_distance_terms ζ x y) hs
  intro i
  by_cases hi : r < i.natAbs
  · rw [if_pos hi]
    exact mul_le_of_le_one_right (weight_pos i).le (coordinate_le_one ζ _ _)
  · rw [if_neg hi, h i (le_of_not_gt hi), coordinate_self, mul_zero]

/-- A disagreement inside the centered window gives the lower bound
(2^{-r}delta). This is the other comparison in `propositionn1`. -/
theorem distance_ge_of_disagree (ζ : A → E) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a b : A, a ≠ b → δ ≤ coordinateDistance ζ a b)
    (x y : ℤ → A) {i : ℤ} {r : ℕ} (hi : i.natAbs ≤ r) (hne : x i ≠ y i) :
    (1 / 2 : ℝ) ^ r * δ ≤ distance ζ x y := by
  apply le_trans _ (coordinate_term_le_distance ζ x y i)
  apply mul_le_mul _ (hsep _ _ hne) hδ.le (weight_pos i).le
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hi

variable [Fintype A]

private theorem minimum_separation (ζ : A → E) (hinj : Function.Injective ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : A, a ≠ b → δ ≤ coordinateDistance ζ a b := by
  classical
  let pairs := (Finset.univ : Finset (A × A)).filter fun p => p.1 ≠ p.2
  by_cases he : pairs.Nonempty
  · obtain ⟨p, hp, hmin⟩ := pairs.exists_min_image (fun p => coordinateDistance ζ p.1 p.2) he
    have hp' : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    refine ⟨_, coordinate_pos ζ hinj hp', fun a b hab => hmin (a, b) ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a b hab
    exact (he ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩).elim

variable [TopologicalSpace A] [DiscreteTopology A]

private def window (r : ℕ) : Finset ℤ := Finset.Icc (-(r : ℤ)) (r : ℤ)

private theorem mem_window (i : ℤ) (r : ℕ) : i ∈ window r ↔ i.natAbs ≤ r := by
  simp only [window, Finset.mem_Icc]
  omega

/-- The metric balls and the finite-coordinate neighborhoods induce
the same topology. Both directions use the centered-window estimates
from the dissertation. -/
theorem isOpen_iff_distance (ζ : A → E) (hinj : Function.Injective ζ) (s : Set (ℤ → A)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > (0 : ℝ), ∀ y, distance ζ x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hs x hx
    let r := I.sup Int.natAbs
    obtain ⟨δ, hδ, hsep⟩ := minimum_separation ζ hinj
    refine ⟨(1 / 2 : ℝ) ^ r * δ, mul_pos (pow_pos (by norm_num) _) hδ, ?_⟩
    intro y hy
    apply hsub
    intro i hi
    have hir : i.natAbs ≤ r := Finset.le_sup (Finset.mem_coe.mp hi)
    have he : x i = y i := by
      by_contra hne
      exact (not_lt_of_ge (distance_ge_of_disagree ζ hδ hsep x y hir hne)) hy
    rw [← he]
    exact (hu i (Finset.mem_coe.mp hi)).2
  · intro hs
    apply isOpen_pi_iff.mpr
    intro x hx
    obtain ⟨ε, hε, hb⟩ := hs x hx
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 2 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨window r, fun i => {x i}, fun i _ => ⟨isOpen_discrete _, by simp⟩, ?_⟩
    intro y hy
    apply hb
    have he : ∀ i, i.natAbs ≤ r → x i = y i := by
      intro i hi
      exact (Set.mem_singleton_iff.mp (hy i (Finset.mem_coe.mpr ((mem_window i r).mpr hi)))).symm
    exact (distance_le_of_agree ζ x y r he).trans_lt (by linarith)

/-- The actual metric with the preexisting product topology. -/
def metricSpace (ζ : A → E) (hinj : Function.Injective ζ) : MetricSpace (ℤ → A) :=
  MetricSpace.ofDistTopology (distance ζ) (distance_self ζ) (distance_comm ζ)
    (distance_triangle ζ) (isOpen_iff_distance ζ hinj) (eq_of_distance_eq_zero ζ hinj)

/-- A closed subshift is compact, hence complete in the symbolic-lattice
metric. The compactness argument is the product theorem for finite
discrete alphabets. -/
theorem compact_and_complete_of_closed (ζ : A → E) (hinj : Function.Injective ζ)
    (s : Set (ℤ → A)) (hs : IsClosed s) :
    letI := metricSpace ζ hinj
    IsCompact s ∧ IsComplete s := by
  letI := metricSpace ζ hinj
  have hc : IsCompact s := hs.isCompact
  exact ⟨hc, hc.isComplete⟩

/-- The shift is 2-Lipschitz for the symbolic-lattice metric. -/
theorem shift_lipschitz (ζ : A → E) (hinj : Function.Injective ζ) :
    letI := metricSpace ζ hinj
    LipschitzWith 2 (shift : (ℤ → A) → (ℤ → A)) := by
  letI := metricSpace ζ hinj
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact shift_distance_le ζ x y

/-- The map into the Banach space is Lipschitz for the same metric. -/
theorem embedding_lipschitz [NormedSpace ℝ E] [CompleteSpace E]
    (ζ : A → E) (hinj : Function.Injective ζ) :
    letI := metricSpace ζ hinj
    LipschitzWith (Real.toNNReal (max 1 (diameter ζ))) (embedding ζ) := by
  letI := metricSpace ζ hinj
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hC : (0 : ℝ) ≤ max 1 (diameter ζ) := zero_le_one.trans (le_max_left _ _)
  change dist (embedding ζ x) (embedding ζ y) ≤
    (Real.toNNReal (max 1 (diameter ζ)) : ℝ) * distance ζ x y
  rw [Real.coe_toNNReal _ hC, dist_eq_norm]
  exact embedding_norm_sub_le ζ x y

end Cylinders

end Thesis.SymbolicLattice
