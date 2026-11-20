import Thesis.FibonacciGoldenLimits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

open Filter Topology
open scoped goldenRatio

namespace Thesis.Fibonacci

private theorem fib_succ_pos (n : Nat) : 0 < fib (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 0 < fib n + fib (n + 1)
    omega

/-- Binet's exact error for the unframed Fibonacci words in the
paragraph following thm1Asymptotic. -/
theorem golden_unframed_density_error (m : Nat) :
    ((word m).count .a : ℝ) / (word m).length - 1 / φ =
      -ψ ^ (m + 1) / (φ * (fib (m + 2) : ℝ)) := by
  rw [word_count_a, word_length]
  have h := previousRatio_binet gold_add_goldConj gold_mul_goldConj (m + 1)
  change (fib (m + 1) : ℝ) / (fib (m + 2) : ℝ) =
    1 / φ - ψ ^ (m + 1) / (φ * (fib (m + 2) : ℝ)) at h
  rw [h, neg_div]
  ring

/-- The sign of the unframed error alternates with m. -/
theorem golden_unframed_alternating (m : Nat) :
    ((word m).count .a : ℝ) / (word m).length - 1 / φ =
      (-1 : ℝ) ^ m * ((φ⁻¹) ^ (m + 1) / (φ * (fib (m + 2) : ℝ))) := by
  rw [golden_unframed_density_error]
  have hψ : ψ = -φ⁻¹ := (reciprocal_and_conjugate gold_mul_goldConj one_lt_gold).2.2
  rw [hψ, neg_pow, pow_succ (-1 : ℝ) m]
  ring

/-- The order φ^(-2m) for the unframed error, from the bound on the
Fibonacci denominator obtained from Binet's formula. -/
theorem golden_unframed_error_bound (m : Nat) :
    |((word m).count .a : ℝ) / (word m).length - 1 / φ| ≤
      ((φ - ψ) / (φ * (1 - φ⁻¹))) * ((φ⁻¹) ^ 2) ^ m := by
  have ⟨hi, hi1, hψ⟩ := reciprocal_and_conjugate gold_mul_goldConj one_lt_gold
  have hφ : 0 < φ := zero_lt_one.trans one_lt_gold
  have hφψ : 0 < φ - ψ := by rw [hψ]; linarith
  have hD : 0 < 1 - φ⁻¹ := by linarith
  have hp : 0 < φ ^ m := pow_pos hφ _
  have hF : 0 < (fib (m + 2) : ℝ) := by exact_mod_cast fib_succ_pos (m + 1)
  have hstep : φ ^ m ≤ φ ^ (m + 2) := pow_le_pow_right₀ one_lt_gold.le (by omega)
  have hlow := (mul_le_mul_of_nonneg_left hstep hD.le).trans
    (binet_growth_lower gold_add_goldConj gold_mul_goldConj one_lt_gold (m + 1))
  have hden : (φ * ((1 - φ⁻¹) * φ ^ m)) / (φ - ψ) ≤ φ * (fib (m + 2) : ℝ) := by
    apply (div_le_iff₀ hφψ).2
    have hh := mul_le_mul_of_nonneg_left hlow hφ.le
    linarith only [hh, show φ * ((φ - ψ) * (fib (m + 2) : ℝ)) =
      φ * (fib (m + 2) : ℝ) * (φ - ψ) by ring]
  rw [golden_unframed_density_error, abs_div, abs_neg, abs_pow, hψ, abs_neg,
    abs_of_pos hi, abs_of_pos (mul_pos hφ hF)]
  calc
    _ ≤ (φ⁻¹) ^ m / ((φ * ((1 - φ⁻¹) * φ ^ m)) / (φ - ψ)) := by
      have hnum : (φ⁻¹) ^ (m + 1) ≤ (φ⁻¹) ^ m := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hi.le _) hi1.le
      apply (div_le_div_of_nonneg_right hnum (mul_pos hφ hF).le).trans
      exact div_le_div_of_nonneg_left (pow_nonneg hi.le _)
        (div_pos (mul_pos hφ (mul_pos hD hp)) hφψ) hden
    _ = _ := by
      rw [← pow_mul, Nat.mul_comm 2 m, pow_mul]
      simp only [inv_pow]
      rw [hψ, ← inv_pow (φ ^ m) 2]
      let A := φ * (1 - φ⁻¹)
      let B := φ - -φ⁻¹
      let P := φ ^ m
      have he : φ * ((1 - φ⁻¹) * φ ^ m) = A * P := by unfold A P; ring
      rw [he]
      change P⁻¹ / (A * P / B) = B / A * (P⁻¹)^2
      have hA : A ≠ 0 := (mul_pos hφ hD).ne'
      have hP : P ≠ 0 := hp.ne'
      have hB : B ≠ 0 := by
        change φ - -φ⁻¹ ≠ 0
        rw [← hψ]
        exact hφψ.ne'
      field_simp [hA, hP, hB]
      ring

private theorem unframed_complement (m : Nat) :
    ((word m).count .b : ℝ) / (word m).length =
      1 - ((word m).count .a : ℝ) / (word m).length := by
  rw [word_count_a, word_count_b, word_length]
  have hp : (0 : ℝ) < (fib (m + 2) : ℝ) := by exact_mod_cast fib_succ_pos (m + 1)
  field_simp [hp.ne']
  rw [fib, Nat.cast_add]
  ring

/-- The two limits in the unframed columns of the table. -/
theorem golden_unframed_density_limits :
    Tendsto (fun m : Nat => ((word m).count .a : ℝ) / (word m).length) atTop (𝓝 (1 / φ)) ∧
    Tendsto (fun m : Nat => ((word m).count .b : ℝ) / (word m).length) atTop (𝓝 ((φ⁻¹) ^ 2)) := by
  have ⟨hi, hi1, _⟩ := reciprocal_and_conjugate gold_mul_goldConj one_lt_gold
  have hq : (φ⁻¹) ^ 2 < 1 := by simpa using pow_lt_pow_left₀ hi1 hi.le (by decide : (2 : Nat) ≠ 0)
  have hbound := (tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hi.le 2) hq).const_mul
    ((φ - ψ) / (φ * (1 - φ⁻¹)))
  rw [mul_zero] at hbound
  have ha : Tendsto (fun m : Nat => ((word m).count .a : ℝ) / (word m).length) atTop (𝓝 (1 / φ)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hbound.eventually (gt_mem_nhds hε))
    exact ⟨M, fun m hm => by rw [Real.dist_eq]; exact (golden_unframed_error_bound m).trans_lt (hM m hm)⟩
  have hcomp : (φ⁻¹) ^ 2 = 1 - 1 / φ := by
    rw [golden_inverse_square gold_add_goldConj gold_mul_goldConj, one_div, inv_gold]
    linarith [gold_add_goldConj]
  exact ⟨ha, by simpa only [hcomp, unframed_complement] using ha.const_sub (1 : ℝ)⟩

/-- The strict half-millionth intervals for the last line of
tab002densitiesASm, certifying the printed rounding in all four columns. -/
theorem density_table_limit_rounding :
    (1236067 : ℝ) / 2000000 < 1 / φ ∧ 1 / φ < 1236069 / 2000000 ∧
    (763931 : ℝ) / 2000000 < (φ⁻¹) ^ 2 ∧ (φ⁻¹) ^ 2 < 763933 / 2000000 := by
  have hlo : (2236067 : ℝ) / 1000000 < Real.sqrt 5 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hhi : Real.sqrt 5 < (2236069 : ℝ) / 1000000 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  rw [golden_inverse_square gold_add_goldConj gold_mul_goldConj, one_div, inv_gold]
  unfold goldenConj goldenRatio
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Thesis.Fibonacci
