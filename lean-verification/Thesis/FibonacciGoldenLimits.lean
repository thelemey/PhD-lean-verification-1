import Thesis.FibonacciSeries
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open Filter Topology
open scoped goldenRatio BigOperators Asymptotics

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

/-- The two error rates in thm1Asymptotic, in standard big-O notation. -/
theorem golden_framed_density_rates :
    let errA := fun m : Nat => ((framed m).count .a : ℝ) / (framed m).length - 1 / φ
    let errB := fun m : Nat => ((framed m).count .b : ℝ) / (framed m).length - φ⁻¹ ^ 2
    let fibRate := fun m : Nat => (1 : ℝ) / fib (m + 2)
    let powRate := fun m : Nat => φ⁻¹ ^ m
    (errA =O[atTop] fibRate ∧ errB =O[atTop] fibRate) ∧
      (errA =O[atTop] powRate ∧ errB =O[atTop] powRate) := by
  intro errA errB fibRate powRate
  have both (g : Nat → ℝ) (C : ℝ) (hb : ∀ m, |errA m| ≤ C * |g m|) :
      errA =O[atTop] g ∧ errB =O[atTop] g := by
    refine ⟨Asymptotics.IsBigO.of_bound C (Eventually.of_forall ?_),
      Asymptotics.IsBigO.of_bound C (Eventually.of_forall ?_)⟩
    · intro m
      simpa only [Real.norm_eq_abs] using hb m
    · intro m
      simp only [Real.norm_eq_abs]
      change |((framed m).count .b : ℝ) / (framed m).length - φ⁻¹ ^ 2| ≤ _
      rw [framed_second_density_error gold_add_goldConj gold_mul_goldConj one_lt_gold m]
      exact hb m
  have hφ : 0 < φ := zero_lt_one.trans one_lt_gold
  have hφi : 0 ≤ φ⁻¹ := inv_nonneg.mpr hφ.le
  constructor
  · apply both fibRate (2 / φ)
    intro m
    have hf : 0 < (fib (m + 2) : ℝ) := by exact_mod_cast fib_positive (m + 1)
    have hden : φ * (fib (m + 2) : ℝ) ≤ φ * ((fib (m + 2) : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hφ.le
    have he : 2 / (φ * (fib (m + 2) : ℝ)) = (2 / φ) * fibRate m := by
      dsimp only [fibRate]
      rw [← div_div, div_eq_mul_one_div]
    rw [abs_of_nonneg (one_div_nonneg.mpr hf.le)]
    exact (framed_density_error_bound gold_add_goldConj gold_mul_goldConj one_lt_gold m).trans
      ((div_le_div_of_nonneg_left (by norm_num) (mul_pos hφ hf) hden).trans_eq he)
  · let C := 2 * (φ - ψ) / (φ * (1 - φ⁻¹))
    apply both powRate (C * φ⁻¹ ^ 2)
    intro m
    rw [abs_of_nonneg (pow_nonneg hφi _)]
    have he : C * φ⁻¹ ^ (m + 2) = (C * φ⁻¹ ^ 2) * powRate m := by
      dsimp only [powRate]
      rw [pow_add]
      ring
    exact (framed_density_exponential_bound gold_add_goldConj gold_mul_goldConj
      one_lt_gold m).trans_eq he

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

/-- The big-O remainder in thm:millin after K+1 terms. -/
theorem millin_tsum_remainder_isBigO (m : Nat) (hm : 0 < m) :
    (fun K : Nat => (∑' i : Nat, (1 : ℝ) / fib (m * 2 ^ (i + 1))) - millinPartial m K)
      =O[atTop] fun K : Nat => φ⁻¹ ^ (m * 2 ^ K) := by
  apply Asymptotics.IsBigO.of_bound 1
  refine Eventually.of_forall fun K => ?_
  have hp : 0 < φ⁻¹ := inv_pos.mpr (zero_lt_one.trans one_lt_gold)
  have hlt : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_gold
  have hstep : 2 ^ K < (2 : Nat) ^ (K + 1) := by
    rw [pow_succ]
    have := Nat.two_pow_pos K
    omega
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hp.le _), one_mul]
  exact (millin_tsum_remainder m hm K).trans
    (pow_lt_pow_right_of_lt_one₀ hp hlt (Nat.mul_lt_mul_of_pos_left hstep hm)).le

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
