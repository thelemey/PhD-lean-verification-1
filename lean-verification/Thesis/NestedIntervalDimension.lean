import Thesis.NestedIntervalCodes
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring

open Set Filter Metric
open scoped Topology NNReal ENNReal

namespace Thesis.NestedIntervals

variable {B : ℕ}

private theorem exists_first_difference {v w : ℕ → Fin B} (h : v ≠ w) :
    ∃ n, (∀ j < n, v j = w j) ∧ v n ≠ w n := by
  classical
  have hex : ∃ n, v n ≠ w n := Function.ne_iff.1 h
  exact ⟨Nat.find hex, fun j hj => not_not.1 (Nat.find_min hex hj), Nat.find_spec hex⟩

/-- The interval addresses of an ordinary subdivision into B equal pieces. -/
noncomputable def equalSubdivision (hB : 1 < B) : IntervalCode B := by
  have hB' : (1 : ℝ) < B := by exact_mod_cast hB
  have hpos : 0 < (B : ℝ) := zero_lt_one.trans hB'
  refine ⟨0, fun n => 1 / (B : ℝ) ^ n, fun _ => by positivity, ?_,
    fun n x j => x + (j.val : ℝ) * (1 / (B : ℝ) ^ (n + 1)), ?_⟩
  · have h := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hpos.le) (inv_lt_one_of_one_lt₀ hB')
    simpa only [one_div, inv_pow] using h
  · intro n x j
    have hJ : (j.val : ℝ) + 1 ≤ B := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
    have hu : 0 < (1 : ℝ) / (B : ℝ) ^ (n + 1) := by positivity
    have he : (B : ℝ) * (1 / (B : ℝ) ^ (n + 1)) = 1 / (B : ℝ) ^ n := by
      rw [pow_succ, ← div_div, mul_div_cancel₀ _ hpos.ne']
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · have h := mul_le_mul_of_nonneg_right hJ hu.le
      rw [he] at h
      rw [add_mul, one_mul] at h
      linarith

private theorem subdivision_cover (hB : 1 < B) (n : ℕ) (x y : ℝ)
    (hy : y ∈ Icc x (x + (equalSubdivision hB).width n)) :
    ∃ j : Fin B, y ∈ Icc ((equalSubdivision hB).child n x j)
      ((equalSubdivision hB).child n x j + (equalSubdivision hB).width (n + 1)) := by
  let L := (equalSubdivision hB).width (n + 1)
  let t := (y - x) / L
  have hL : 0 < L := (equalSubdivision hB).width_pos _
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hy.1) hL.le
  have hB0 : 0 < (B : ℝ) := by exact_mod_cast (zero_lt_one.trans hB)
  have he : (B : ℝ) * L = (equalSubdivision hB).width n := by
    change (B : ℝ) * (1 / (B : ℝ) ^ (n + 1)) = 1 / (B : ℝ) ^ n
    rw [pow_succ, ← div_div, mul_div_cancel₀ _ hB0.ne']
  have htB : t ≤ (B : ℝ) := by
    apply (div_le_iff₀ hL).2
    linarith [hy.2]
  let j := min ⌊t⌋₊ (B - 1)
  have hjB : j < B := (min_le_right _ _).trans_lt (by omega)
  have hlow : (j : ℝ) ≤ t :=
    (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le ht0)
  have hhigh : t ≤ (j : ℝ) + 1 := by
    by_cases he : ⌊t⌋₊ ≤ B - 1
    · have he' : j = ⌊t⌋₊ := min_eq_left he
      rw [he']
      exact (Nat.lt_floor_add_one t).le
    · have he' : j = B - 1 := min_eq_right (le_of_not_ge he)
      rw [he', Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one]
      linarith
  refine ⟨⟨j, hjB⟩, ?_, ?_⟩
  · change x + (j : ℝ) * L ≤ y
    have h := (le_div_iff₀ hL).1 hlow
    linarith
  · change y ≤ x + (j : ℝ) * L + L
    have h := (div_le_iff₀ hL).1 hhigh
    rw [add_mul, one_mul] at h
    linarith

/-- The dimension lower bound comes from a Hölder surjection onto the
unit interval. Agreement at level n bounds the image distance, and
disagreement at the next level bounds the source distance from below. -/
theorem dimH_range_ge_of_separated (T : IntervalCode B) (hB : 1 < B)
    (hsep : ∀ n x i j, i ≠ j → 2 * T.width (n + 1) ≤ dist (T.child n x i) (T.child n x j))
    {r C : ℝ≥0} (hr : 0 < r)
    (hscale : ∀ n : ℕ, 1 / (B : ℝ) ^ n ≤ (C : ℝ) * T.width (n + 1) ^ (r : ℝ)) :
    (r : ℝ≥0∞) ≤ dimH (range T.point) := by
  classical
  let U := equalSubdivision hB
  have hinj : Function.Injective T.point := by
    intro v w he
    by_contra hn
    obtain ⟨n, hp, hd⟩ := exists_first_difference hn
    have h := T.point_dist_ge_of_separation hsep hp hd
    rw [he, dist_self] at h
    exact (not_le_of_gt (T.width_pos _)) h
  let F := fun x => if hx : x ∈ range T.point then U.point hx.choose else 0
  have hF (v : ℕ → Fin B) : F (T.point v) = U.point v := by
    have hv : T.point v ∈ range T.point := ⟨v, rfl⟩
    simp only [F, dif_pos hv]
    exact congrArg U.point (hinj hv.choose_spec)
  have hh : HolderOnWith C r F (range T.point) := by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [hF, hF, edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal (p := C), ← ENNReal.ofReal_mul C.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    by_cases h : v = w
    · subst w
      rw [dist_self]
      positivity
    · obtain ⟨n, hn, hd⟩ := exists_first_difference h
      have h₁ := U.point_dist_le_of_agreement hn
      have h₂ := T.point_dist_ge_of_separation hsep hn hd
      exact (h₁.trans (hscale n)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (T.width_pos _).le h₂ r.coe_nonneg) C.coe_nonneg)
  have hcover : Icc (0 : ℝ) 1 ⊆ F '' range T.point := by
    intro y hy
    have hUy : y ∈ Icc U.origin (U.origin + U.width 0) := by
      simpa [U, equalSubdivision] using hy
    obtain ⟨v, hv⟩ := U.exists_address (subdivision_cover hB) hUy
    exact ⟨T.point v, ⟨v, rfl⟩, (hF v).trans hv⟩
  have hdim : dimH (Icc (0 : ℝ) 1) = 1 := by
    rw [Real.dimH_of_nonempty_interior (show (interior (Icc (0 : ℝ) 1)).Nonempty from by
      rw [interior_Icc]
      exact nonempty_Ioo.2 zero_lt_one), Module.finrank_self, Nat.cast_one]
  have hm := (dimH_mono hcover).trans (hh.dimH_image_le hr)
  rw [hdim, ENNReal.le_div_iff_mul_le] at hm
  · simpa only [one_mul] using hm
  · exact Or.inl (mt ENNReal.coe_eq_zero.1 hr.ne')
  · exact Or.inl ENNReal.coe_ne_top

end Thesis.NestedIntervals
