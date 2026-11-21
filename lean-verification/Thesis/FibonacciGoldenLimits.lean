import Thesis.FibonacciSeries
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open Filter Topology
open scoped goldenRatio BigOperators

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

/-- The exact two densities in thm1Asymptotic, with the actual roots φ
and ψ and the normalization of F used in the source. -/
theorem golden_framed_densities_exact (m : Nat) (hm : 0 < m) :
    let densityA := ((framed m).count .a : ℝ) / (framed m).length
    let densityB := ((framed m).count .b : ℝ) / (framed m).length
    densityA = ((fib (m + 1) : ℝ) + 1) / ((fib (m + 2) : ℝ) + 2) ∧
      densityA = 1 / φ - (φ⁻¹ ^ 2 + ψ ^ (m + 1)) / (φ * ((fib (m + 2) : ℝ) + 2)) ∧
      densityB = 1 - densityA ∧ densityA < 1 / φ := by
  dsimp only
  refine ⟨?_, ?_, framed_density_complement m,
    framed_density_lt gold_add_goldConj gold_mul_goldConj one_lt_gold hm⟩
  · rw [framed_count_a, framed_length]
    push_cast
    rfl
  · have he := congrArg (fun x : ℝ => x + 1 / φ)
      (framed_density_error_real gold_add_goldConj gold_mul_goldConj one_lt_gold m)
    dsimp only at he
    rw [sub_add_cancel] at he
    rw [he, neg_div, add_comm, sub_eq_add_neg]

/-- The infinite sum in thm:millin, indexed from k = 1 in the source. -/
theorem millin_hasSum (m : Nat) (hm : 0 < m) :
    HasSum (fun i : Nat => (1 : ℝ) / fib (m * 2 ^ (i + 1)))
      ((fib (m - 1) : ℝ) / fib m - 1 / φ + (1 - (-1 : ℝ) ^ m) / fib (2 * m)) := by
  change HasSum _ (millinLimit φ m)
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).2
  apply (tendsto_add_atTop_iff_nat 1).1
  exact golden_millin_limit m hm

theorem millin_tsum (m : Nat) (hm : 0 < m) :
    (∑' i : Nat, (1 : ℝ) / fib (m * 2 ^ (i + 1))) =
      (fib (m - 1) : ℝ) / fib m - 1 / φ + (1 - (-1 : ℝ) ^ m) / fib (2 * m) :=
  (millin_hasSum m hm).tsum_eq

/-- The remainder after K+1 terms, now expressed using the infinite series. -/
theorem millin_tsum_remainder (m : Nat) (hm : 0 < m) (K : Nat) :
    |(∑' i : Nat, (1 : ℝ) / fib (m * 2 ^ (i + 1))) - millinPartial m K| ≤
      φ⁻¹ ^ (m * 2 ^ (K + 1)) := by
  rw [millin_tsum m hm]
  exact millin_remainder_bound gold_add_goldConj gold_mul_goldConj one_lt_gold m hm K

/-- The infinite sum in prop:sum2r, obtained from its finite alternating
telescoping identity and the limit of the alternating tail. -/
theorem even_shift_hasSum (r : Nat) (hr : 0 < r) :
    HasSum (fun i : Nat => (1 : ℝ) / ((fib (i + 1) : ℝ) * fib (i + 1 + 2 * r)))
      ((1 : ℝ) / fib (2 * r) *
        ∑ i ∈ Finset.range r, (1 : ℝ) / ((fib (2 * i + 1) : ℝ) * fib (2 * i + 2))) := by
  have h : HasSum (fun i : Nat => (1 : ℝ) / ((fib (i + 1) : ℝ) * fib (i + 1 + 2 * r)))
      (evenShiftLimit r) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).2 (even_shift_limit r hr)
  convert h using 1
  unfold evenShiftLimit
  ring

theorem even_shift_tsum (r : Nat) (hr : 0 < r) :
    (∑' i : Nat, (1 : ℝ) / ((fib (i + 1) : ℝ) * fib (i + 1 + 2 * r))) =
      (1 : ℝ) / fib (2 * r) *
        ∑ i ∈ Finset.range r, (1 : ℝ) / ((fib (2 * i + 1) : ℝ) * fib (2 * i + 2)) :=
  (even_shift_hasSum r hr).tsum_eq

end Thesis.Fibonacci
