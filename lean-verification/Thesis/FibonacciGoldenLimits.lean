import Thesis.FibonacciSeries
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open Filter Topology
open scoped goldenRatio

namespace Thesis.Fibonacci

/-- The ordinary real limits in `thm1Asymptotic`, specialized to the
golden ratio and its conjugate from mathlib. -/
theorem golden_framed_density_limits :
    Tendsto (fun m : Nat => ((framed m).count .a : ℝ) / (framed m).length)
      atTop (𝓝 (1 / φ)) ∧
    Tendsto (fun m : Nat => ((framed m).count .b : ℝ) / (framed m).length)
      atTop (𝓝 ((φ⁻¹) ^ 2)) := by
  constructor <;> apply Metric.tendsto_atTop.2 <;> intro ε hε
  · obtain ⟨K, hK⟩ := framed_densities_converge gold_add_goldConj gold_mul_goldConj
      one_lt_gold ε hε
    exact ⟨K, fun m hm => by simpa only [Real.dist_eq] using (hK m hm).1⟩
  · obtain ⟨K, hK⟩ := framed_densities_converge gold_add_goldConj gold_mul_goldConj
      one_lt_gold ε hε
    exact ⟨K, fun m hm => by simpa only [Real.dist_eq] using (hK m hm).2⟩

/-- The limit of the Millin partial sums at the actual golden ratio. -/
theorem golden_millin_limit (m : Nat) (hm : 0 < m) :
    Tendsto (millinPartial m) atTop (𝓝 (millinLimit φ m)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨K, hK⟩ := millin_converges gold_add_goldConj gold_mul_goldConj one_lt_gold m hm ε hε
  exact ⟨K, fun N hN => by simpa only [Real.dist_eq, abs_sub_comm] using hK N hN⟩

/-- The limit in the even-shift series `prop:sum2r`. -/
theorem even_shift_limit (r : Nat) (hr : 0 < r) :
    Tendsto (evenShiftPartial r) atTop (𝓝 (evenShiftLimit r)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨K, hK⟩ := even_shift_converges gold_add_goldConj gold_mul_goldConj
    one_lt_gold r hr ε hε
  exact ⟨K, fun N hN => by simpa only [Real.dist_eq] using hK N hN⟩

end Thesis.Fibonacci
