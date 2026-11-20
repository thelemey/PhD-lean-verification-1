import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators

noncomputable section

namespace Thesis.SymbolicLattice

variable {A E : Type*} [NormedAddCommGroup E]

/-- The weight (2^{-|i|}) in the symbolic-lattice distance. -/
def weight (i : ℤ) : ℝ := (1 / 2 : ℝ) ^ i.natAbs

theorem weight_pos (i : ℤ) : 0 < weight i :=
  pow_pos (by norm_num) _

private theorem geom_summable : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

private theorem geom_summable_succ : Summable fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) := by
  simpa only [pow_succ] using geom_summable.mul_right (1 / 2)

theorem summable_weight : Summable weight := by
  apply Summable.of_nat_of_neg_add_one
  · simpa only [weight, Int.natAbs_ofNat] using geom_summable
  · have he (n : ℕ) : (-(↑n + 1) : ℤ).natAbs = n + 1 := by omega
    simpa only [weight, he] using geom_summable_succ

/-- The truncated coordinate distance, as in `sec:dSL`. -/
def coordinateDistance (ζ : A → E) (a b : A) : ℝ :=
  min 1 ‖ζ a - ζ b‖

theorem coordinate_nonneg (ζ : A → E) (a b : A) : 0 ≤ coordinateDistance ζ a b :=
  le_min zero_le_one (norm_nonneg _)

theorem coordinate_le_one (ζ : A → E) (a b : A) : coordinateDistance ζ a b ≤ 1 :=
  min_le_left _ _

@[simp] theorem coordinate_self (ζ : A → E) (a : A) : coordinateDistance ζ a a = 0 := by
  simp [coordinateDistance]

theorem coordinate_comm (ζ : A → E) (a b : A) :
    coordinateDistance ζ a b = coordinateDistance ζ b a := by
  unfold coordinateDistance
  rw [norm_sub_rev]

theorem coordinate_pos (ζ : A → E) (hζ : Function.Injective ζ) {a b : A} (h : a ≠ b) :
    0 < coordinateDistance ζ a b := by
  apply lt_min zero_lt_one
  exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => h (hζ he)))

theorem coordinate_triangle (ζ : A → E) (a b c : A) :
    coordinateDistance ζ a c ≤ coordinateDistance ζ a b + coordinateDistance ζ b c := by
  by_cases hab : ‖ζ a - ζ b‖ ≤ 1
  · by_cases hbc : ‖ζ b - ζ c‖ ≤ 1
    · unfold coordinateDistance
      rw [min_eq_right hab, min_eq_right hbc]
      exact (min_le_right _ _).trans
        (by simpa only [dist_eq_norm] using dist_triangle (ζ a) (ζ b) (ζ c))
    · have he : coordinateDistance ζ b c = 1 := min_eq_left (le_of_not_ge hbc)
      rw [he]
      linarith [coordinate_le_one ζ a c, coordinate_nonneg ζ a b]
  · have he : coordinateDistance ζ a b = 1 := min_eq_left (le_of_not_ge hab)
    rw [he]
    linarith [coordinate_le_one ζ a c, coordinate_nonneg ζ b c]

def distance (ζ : A → E) (x y : ℤ → A) : ℝ :=
  ∑' i, weight i * coordinateDistance ζ (x i) (y i)

theorem summable_distance_terms (ζ : A → E) (x y : ℤ → A) :
    Summable (fun i => weight i * coordinateDistance ζ (x i) (y i)) := by
  apply Summable.of_nonneg_of_le _ _ summable_weight
  · exact fun i => mul_nonneg (weight_pos i).le (coordinate_nonneg ζ _ _)
  · intro i
    exact mul_le_of_le_one_right (weight_pos i).le (coordinate_le_one ζ _ _)

theorem distance_nonneg (ζ : A → E) (x y : ℤ → A) : 0 ≤ distance ζ x y :=
  tsum_nonneg fun i => mul_nonneg (weight_pos i).le (coordinate_nonneg ζ _ _)

theorem coordinate_term_le_distance (ζ : A → E) (x y : ℤ → A) (i : ℤ) :
    weight i * coordinateDistance ζ (x i) (y i) ≤ distance ζ x y := by
  exact (summable_distance_terms ζ x y).le_tsum i
    (fun j _ => mul_nonneg (weight_pos j).le (coordinate_nonneg ζ _ _))

@[simp] theorem distance_self (ζ : A → E) (x : ℤ → A) : distance ζ x x = 0 := by
  simp [distance]

theorem distance_comm (ζ : A → E) (x y : ℤ → A) : distance ζ x y = distance ζ y x := by
  unfold distance
  congr with i
  rw [coordinate_comm]

theorem distance_triangle (ζ : A → E) (x y z : ℤ → A) :
    distance ζ x z ≤ distance ζ x y + distance ζ y z := by
  unfold distance
  rw [← (summable_distance_terms ζ x y).tsum_add (summable_distance_terms ζ y z)]
  refine Summable.tsum_le_tsum ?_ (summable_distance_terms ζ x z)
    ((summable_distance_terms ζ x y).add (summable_distance_terms ζ y z))
  intro i
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (coordinate_triangle ζ _ _ _) (weight_pos i).le

theorem eq_of_distance_eq_zero (ζ : A → E) (hζ : Function.Injective ζ)
    (x y : ℤ → A) (h : distance ζ x y = 0) : x = y := by
  funext i
  by_contra he
  have hl := coordinate_term_le_distance ζ x y i
  rw [h] at hl
  exact (not_lt_of_ge hl) (mul_pos (weight_pos i) (coordinate_pos ζ hζ he))

/-- The left shift moves the letter at (i+1) to (i). -/
def shift (x : ℤ → A) (i : ℤ) : A := x (i + 1)

private theorem weight_sub_one_le (i : ℤ) : weight (i - 1) ≤ 2 * weight i := by
  have h := Int.natAbs_add_le (i - 1) 1
  have hi : (i - 1 + 1).natAbs = i.natAbs := by rw [sub_add_cancel]
  rw [hi] at h
  simp only [Int.natAbs_one] at h
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) h
  rw [pow_succ] at hp
  unfold weight
  linarith

/-- Proposition `prop:dSLshift` for two-sided words. This is exactly the
change of index (j=i+1) followed by the comparison of weights. -/
theorem shift_distance_le (ζ : A → E) (x y : ℤ → A) :
    distance ζ (shift x) (shift y) ≤ 2 * distance ζ x y := by
  let f : ℤ → ℝ := fun j => weight (j - 1) * coordinateDistance ζ (x j) (y j)
  let e := Equiv.addRight (1 : ℤ)
  have he (i : ℤ) : f (e i) = weight i * coordinateDistance ζ ((shift x) i) ((shift y) i) := by
    dsimp [f, e, shift]
    rw [add_sub_cancel_right]
  have hfs : Summable (fun i : ℤ => f (e i)) := by
    simp_rw [he]
    exact summable_distance_terms ζ _ _
  have hf : Summable f := e.summable_iff.mp hfs
  have hchange : distance ζ (shift x) (shift y) = ∑' j, f j := by
    simp only [distance, ← he]
    exact e.tsum_eq f
  rw [hchange, distance, ← Summable.tsum_mul_left 2 (summable_distance_terms ζ x y)]
  refine Summable.tsum_le_tsum ?_ hf ((summable_distance_terms ζ x y).mul_left 2)
  intro i
  dsimp only [f]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (weight_sub_one_le i) (coordinate_nonneg ζ _ _)

section Embedding

variable [NormedSpace ℝ E] [CompleteSpace E] [Fintype A]

/-- The maximum coordinate distance in the target norm. For an empty
alphabet the supremum is zero. -/
def diameter (ζ : A → E) : ℝ :=
  ↑(Finset.univ.sup fun p : A × A => ‖ζ p.1 - ζ p.2‖₊)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem norm_sub_le_diameter (ζ : A → E) (a b : A) :
    ‖ζ a - ζ b‖ ≤ diameter ζ := by
  exact_mod_cast Finset.le_sup (s := (Finset.univ : Finset (A × A)))
    (f := fun p => ‖ζ p.1 - ζ p.2‖₊) (Finset.mem_univ (a, b))

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem norm_le_scaled_coordinate (ζ : A → E) (a b : A) :
    ‖ζ a - ζ b‖ ≤ max 1 (diameter ζ) * coordinateDistance ζ a b := by
  by_cases h : ‖ζ a - ζ b‖ ≤ 1
  · rw [coordinateDistance, min_eq_right h]
    exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
  · rw [coordinateDistance, min_eq_left (le_of_not_ge h), mul_one]
    exact (norm_sub_le_diameter ζ _ _).trans (le_max_right _ _)

/-- The Banach-space series in the symbolic-lattice metric section. -/
def embedding (ζ : A → E) (x : ℤ → A) : E :=
  ∑' i, weight i • ζ (x i)

private theorem summable_embedding (ζ : A → E) (x : ℤ → A) :
    Summable (fun i => weight i • ζ (x i)) := by
  let R := ∑ a : A, ‖ζ a‖
  apply Summable.of_norm_bounded (fun i => weight i * R) (summable_weight.mul_right R)
  intro i
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos i)]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
    (fun a _ => norm_nonneg (ζ a)) (Finset.mem_univ (x i))) (weight_pos i).le

/-- The Lipschitz estimate in part (ii) of `propositionn1`. -/
theorem embedding_norm_sub_le (ζ : A → E) (x y : ℤ → A) :
    ‖embedding ζ x - embedding ζ y‖ ≤ max 1 (diameter ζ) * distance ζ x y := by
  let g : ℤ → E := fun i => weight i • (ζ (x i) - ζ (y i))
  let C := max 1 (diameter ζ)
  have hg (i : ℤ) : ‖g i‖ ≤ C * (weight i * coordinateDistance ζ (x i) (y i)) := by
    dsimp only [g, C]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos i), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (norm_le_scaled_coordinate ζ _ _) (weight_pos i).le
  have hb := (summable_distance_terms ζ x y).mul_left C
  have hgs : Summable (fun i => ‖g i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hg hb
  unfold embedding distance
  rw [← (summable_embedding ζ x).tsum_sub (summable_embedding ζ y), ←
    Summable.tsum_mul_left C (summable_distance_terms ζ x y)]
  simp only [← smul_sub]
  exact (norm_tsum_le_tsum_norm hgs).trans (Summable.tsum_le_tsum hg hgs hb)

end Embedding

end Thesis.SymbolicLattice
