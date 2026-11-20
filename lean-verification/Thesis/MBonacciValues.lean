import Thesis.MBonacciDensity
import Mathlib.Data.Real.GoldenRatio

open Set

namespace Thesis.MBonacci

private theorem beta_between (n : Nat) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b)
    (hneg : characteristic (n + 2) a < 0) (hpos : 0 < characteristic (n + 2) b) :
    a < beta n ∧ beta n < b := by
  have hc : Continuous (characteristic (n + 2)) := by
    unfold characteristic
    fun_prop
  obtain ⟨x, hx, hroot⟩ := intermediate_value_Icc hab hc.continuousOn
    (show (0 : ℝ) ∈ Icc (characteristic (n + 2) a) (characteristic (n + 2) b) from
      ⟨hneg.le, hpos.le⟩)
  have hx' : 1 < x := ha.trans_le hx.1
  have he := (existsUnique_root (n + 2) (by omega)).unique ⟨hx', hroot⟩ (beta_spec n)
  subst x
  exact ⟨lt_of_le_of_ne hx.1 (fun h => hneg.ne (h ▸ hroot)),
    lt_of_le_of_ne hx.2 (fun h => hpos.ne' (h ▸ hroot))⟩

/-- At m=2 the root in `prop:mbonacci` is the golden ratio. -/
theorem fibonacci_root_eq_goldenRatio : beta 0 = goldenRatio := by
  have hroot : characteristic 2 goldenRatio = 0 := by
    norm_num [characteristic, Finset.sum_range_succ, gold_sq, add_comm]
  exact (existsUnique_root 2 le_rfl).unique (beta_spec 0) ⟨one_lt_gold, hroot⟩

/-- The digits displayed for β₃ in `prop:mbonacci`. -/
theorem tribonacci_root_bounds :
    (18392 : ℝ) / 10000 < beta 1 ∧ beta 1 < 18393 / 10000 := by
  apply beta_between
  all_goals norm_num [characteristic, Finset.sum_range_succ]

/-- An enclosure of β₄ that justifies the rounded value 1.9276
in `prop:mbonacci`. -/
theorem tetranacci_root_bounds :
    (192756 : ℝ) / 100000 < beta 2 ∧ beta 2 < 192757 / 100000 := by
  apply beta_between
  all_goals norm_num [characteristic, Finset.sum_range_succ]

/-- The tetranacci root rounds to 1.9276 to four decimal places. -/
theorem tetranacci_root_rounding :
    (192755 : ℝ) / 100000 < beta 2 ∧ beta 2 < 192765 / 100000 :=
  ⟨(by norm_num : (192755 : ℝ) / 100000 ≤ 192756 / 100000).trans_lt tetranacci_root_bounds.1,
    tetranacci_root_bounds.2.trans_le (by norm_num)⟩

private theorem reciprocal_rounding {x a b lo hi : ℝ} (ha : 0 < a)
    (h : a < x ∧ x < b) (hlo : lo ≤ 1 / b) (hhi : 1 / a ≤ hi) :
    lo < 1 / x ∧ 1 / x < hi :=
  ⟨hlo.trans_lt (one_div_lt_one_div_of_lt (ha.trans h.1) h.2),
    (one_div_lt_one_div_of_lt ha h.1).trans_le hhi⟩

/-- The reciprocal root rounds to 0.5437. -/
theorem tribonacci_density_rounding :
    (54365 : ℝ) / 100000 < 1 / beta 1 ∧ 1 / beta 1 < 54375 / 100000 := by
  apply reciprocal_rounding _ tribonacci_root_bounds <;> norm_num

/-- The reciprocal root rounds to 0.5188. -/
theorem tetranacci_density_rounding :
    (51875 : ℝ) / 100000 < 1 / beta 2 ∧ 1 / beta 2 < 51885 / 100000 := by
  apply reciprocal_rounding _ tetranacci_root_bounds <;> norm_num

end Thesis.MBonacci
