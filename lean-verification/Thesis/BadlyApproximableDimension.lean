import Thesis.NestedIntervalDimension
import Thesis.RationalAvoidanceTree

open Set
open scoped NNReal ENNReal

namespace Thesis.SturmianDensity

open Avoidance NestedIntervals

private theorem exists_branching {r : ℝ} (hr : r < 1) :
    ∃ S B : ℕ, 1 < S ∧ 1 < B ∧ S ^ 2 = 2 * (B + 1) ∧ scale S ^ r ≤ (B : ℝ) := by
  let t : ℝ := 4 ^ (1 / (1 - r))
  obtain ⟨K, hK⟩ := exists_nat_gt (max t 1)
  have hk : (1 : ℝ) < K := (le_max_right _ _).trans_lt hK
  have hkN : 1 < K := by exact_mod_cast hk
  let S := 2 * K
  let B := 2 * K ^ 2 - 1
  have hK2 : 2 ≤ K ^ 2 := by nlinarith
  have hS : 1 < S := by dsimp [S]; omega
  have hB : 1 < B := by dsimp [B]; omega
  have hSB : S ^ 2 = 2 * (B + 1) := by
    have he : S ^ 2 = 4 * K ^ 2 := by dsimp [S]; ring
    rw [he]
    dsimp [B]
    omega
  refine ⟨S, B, hS, hB, hSB, ?_⟩
  have hpos : 0 < scale S := zero_lt_one.trans (scale_gt_one hS)
  have hscale : scale S = 4 * (K : ℝ) ^ 2 := by
    simp only [scale, S, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hKt : t ≤ scale S := by
    rw [hscale]
    exact ((le_max_left _ _).trans hK.le).trans (by nlinarith)
  have hr' : 0 < 1 - r := sub_pos.2 hr
  have ht : t ^ (1 - r) = 4 := by
    dsimp [t]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [div_mul_cancel₀ _ hr'.ne', Real.rpow_one]
  have h4 : 4 ≤ scale S ^ (1 - r) := by
    rw [← ht]
    exact Real.rpow_le_rpow (by dsimp [t]; positivity) hKt hr'.le
  have hm := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hpos.le r)
  rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one] at hm
  have hBK : (K : ℝ) ^ 2 ≤ (B : ℝ) := by
    exact_mod_cast (show K ^ 2 ≤ B by dsimp [B]; omega)
  linarith

private theorem dimH_badlyApproximableSlopes_ge {r : ℝ≥0} (hr : 0 < r) (hr' : r < 1) :
    (r : ℝ≥0∞) ≤ dimH badlyApproximableSlopes := by
  obtain ⟨S, B, hS, hB, hSB, hsize⟩ := exists_branching (show (r : ℝ) < 1 by exact_mod_cast hr')
  have hpos : 0 < scale S := zero_lt_one.trans (scale_gt_one hS)
  let C : ℝ≥0 := ⟨(4 * scale S ^ 2) ^ (r : ℝ), Real.rpow_nonneg (by positivity) _⟩
  have hscale (n : ℕ) : 1 / (B : ℝ) ^ n ≤ (C : ℝ) * (code hS hSB).width (n + 1) ^ (r : ℝ) := by
    have he : (4 * scale S ^ 2) * width S (n + 1) = 1 / scale S ^ n := by
      unfold width
      rw [show n + 1 + 1 = 2 + n by omega, pow_add, ← mul_assoc,
        ← div_div, ← mul_div_assoc, mul_div_cancel₀ _ (by positivity : 4 * scale S ^ 2 ≠ 0)]
    change 1 / (B : ℝ) ^ n ≤ (4 * scale S ^ 2) ^ (r : ℝ) * width S (n + 1) ^ (r : ℝ)
    rw [← Real.mul_rpow (by positivity) (width_pos hS _).le, he,
      Real.div_rpow (by norm_num) (by positivity), Real.one_rpow,
      ← Real.rpow_natCast_mul hpos.le, mul_comm (n : ℝ) (r : ℝ), Real.rpow_mul_natCast hpos.le]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) hsize n)
  exact (dimH_range_ge_of_separated (code hS hSB) hB (code_separation hS hSB)
    hr hscale).trans (dimH_mono (range_code_subset hS hSB))

/-- The Jarník dimension assertion used in cor:palSturm. Each separated
interval construction avoids the appropriate rational denominator band at
each level. Its dimension approaches one as the branching factor grows. -/
theorem dimH_badlyApproximableSlopes_eq_one : dimH badlyApproximableSlopes = 1 := by
  apply le_antisymm
  · exact (dimH_mono (subset_univ _)).trans_eq Real.dimH_univ
  · by_contra! h
    obtain ⟨r, hlo, hhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
    have hr : 0 < r := by exact_mod_cast ((zero_le (dimH badlyApproximableSlopes)).trans_lt hlo)
    have hr' : r < 1 := by exact_mod_cast hhi
    exact (not_le_of_gt hlo) (dimH_badlyApproximableSlopes_ge hr hr')

end Thesis.SturmianDensity
