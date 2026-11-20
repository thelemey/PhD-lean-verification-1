import Thesis.LogOscillationIntegral
import Thesis.WeylCriterion

open Filter Topology

namespace Thesis.FactorialWord

open Thesis.VanDerCorput

/-- For each fixed shift, the limiting modulus of the normalized correlation
in `lem:logfact`. -/
theorem factorial_phase_correlation_tendsto (τ : ℝ) (r : Nat) :
    Tendsto (fun N => ‖normalizedCorrelation (fun n => factorialPhase τ (n + 1)) N r‖)
      atTop (𝓝 (correlationBound τ r)) := by
  apply normalizedCorrelation_tendsto_of_short_mean _ r
  have hcomparison := log_oscillation_normalized_error (τ * (r : ℝ))
  have h := factorial_correlation_limit_of_integral_comparison τ r
    (by simpa only [logOscillation, Nat.cast_succ, mul_assoc] using hcomparison)
  have he (n : Nat) : n + r + 1 = n + 1 + r := by omega
  simpa only [he, correlationBound] using h

/-- The vanishing phase averages obtained by the integral comparison
and the two-window-limit argument in `lem:logfact`. -/
theorem factorial_phase_mean_tendsto (τ : ℝ) (hτ : τ ≠ 0) :
    Tendsto (mean (fun n => factorialPhase τ (n + 1))) atTop (𝓝 0) :=
  mean_tendsto_zero _ (fun _ => Complex.norm_exp_ofReal_mul_I _) τ hτ
    (fun r _ => factorial_phase_correlation_tendsto τ r)

/-- The exponential-average condition of Weyl's criterion, for every
real base (b>1) and every nonzero integer frequency. -/
theorem factorial_log_fourier_tendsto (b : ℝ) (hb : 1 < b)
    (h : ℤ) (hh : h ≠ 0) :
    Tendsto (mean (fun n => oscillation (2 * Real.pi * (h : ℝ) *
      Real.logb b (factorial (n + 1))))) atTop (𝓝 0) := by
  let τ := 2 * Real.pi * (h : ℝ) / Real.log b
  have hτ : τ ≠ 0 := div_ne_zero
    (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.mpr hh))
    (Real.log_pos hb).ne'
  have he : (fun n : Nat => oscillation (2 * Real.pi * (h : ℝ) *
      Real.logb b (factorial (n + 1)))) = fun n => factorialPhase τ (n + 1) := by
    funext n
    unfold factorialPhase Real.logb τ
    congr 1
    ring
  rw [he]
  exact factorial_phase_mean_tendsto τ hτ

/-- The equidistribution claim of `lem:logfact` for every real base. -/
theorem factorial_logs_equidistributed (b : ℝ) (hb : 1 < b) :
    Equidistributed fun n => Real.logb b (factorial (n + 1)) := by
  apply weylCriterion
  exact factorial_log_fourier_tendsto b hb

/-- In `lem:logfact`, every interval of positive length is visited beyond
any prescribed index. -/
theorem factorial_logs_hit_interval (b : ℝ) (hb : 1 < b)
    {α β : ℝ} (hα : 0 ≤ α) (hab : α < β) (hβ : β ≤ 1) (minimum : Nat) :
    ∃ n ≥ minimum, Int.fract (Real.logb b (factorial (n + 1))) ∈ Set.Ico α β :=
  hits_of_equidistributed (factorial_logs_equidistributed b hb) hα hab hβ minimum

/-- Every valid leading block occurs at the start of arbitrarily late
factorials, as stated in `lem:lead`. -/
theorem factorial_leading_prefixes {b : Nat} (hb : 1 < b) : LeadingPrefixes b :=
  leading_prefixes_of_fractional_logs hb
    (fractionalLogHits_of_equidistributed (factorial_logs_equidistributed b (by exact_mod_cast hb)))

/-- Both factorial-word complexities of `mainthm01`, following the
dissertation's proof via equidistribution. -/
theorem full_complexities {b : Nat} (hb : 1 < b) (k : Nat) :
    ∃ words : List (List Nat), words.Nodup ∧ words.length = b ^ k ∧
      (∀ w, w ∈ words ↔ w.length = k ∧ Factor b w) ∧
      (∀ w, w ∈ words ↔ w.length = k ∧ ArithmeticFactor b w) :=
  full_complexities_of_log_distribution hb
    (factorial_logs_equidistributed b (by exact_mod_cast hb)) k

end Thesis.FactorialWord
