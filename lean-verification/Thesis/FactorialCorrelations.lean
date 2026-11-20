import Thesis.FactorialLogarithms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter Topology
open scoped BigOperators

namespace Thesis.FactorialWord

noncomputable def logBlock (n r : Nat) : ℝ :=
  ∑ j ∈ Finset.range r, Real.log ((n : ℝ) + j + 1)

/-- The factorial recurrence gives the block of logarithms in the
correlation calculation of `lem:logfact`. -/
theorem log_factorial_difference (n r : Nat) :
    Real.log (factorial (n + r)) - Real.log (factorial n) = logBlock n r := by
  induction r with
  | zero => simp [logBlock]
  | succ r ih =>
    unfold logBlock at ⊢
    rw [Finset.sum_range_succ]
    change _ = logBlock n r + _
    rw [← ih]
    rw [show n + (r + 1) = (n + r) + 1 by omega, factorial, Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (factorial_pos (n + r)).ne')]
    push_cast
    ring

private theorem log_step_bound (n : Nat) (hn : 0 < n) (j : Nat) :
    0 ≤ Real.log ((n : ℝ) + j + 1) - Real.log n ∧
      Real.log ((n : ℝ) + j + 1) - Real.log n ≤ ((j : ℝ) + 1) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hx : (0 : ℝ) < (n : ℝ) + j + 1 := by linarith
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hnR (by linarith))
  · rw [← Real.log_div hx.ne' hnR.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hx hnR)
    have he : ((n : ℝ) + j + 1) / n - 1 = ((j : ℝ) + 1) / n := by
      field_simp [hnR.ne']
      ring
    exact he ▸ h

/-- A uniform explicit version of the estimate
(sum_{j=1}^r\log(n+j)=r\log n+O_r(n^{-1})) in `lem:logfact`. -/
theorem log_block_error (n r : Nat) (hn : 0 < n) :
    0 ≤ logBlock n r - (r : ℝ) * Real.log n ∧
      logBlock n r - (r : ℝ) * Real.log n ≤ (r : ℝ) ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : logBlock n r - (r : ℝ) * Real.log n =
      ∑ j ∈ Finset.range r, (Real.log ((n : ℝ) + j + 1) - Real.log n) := by
    rw [Finset.sum_sub_distrib]
    simp [logBlock, nsmul_eq_mul]
  rw [he]
  constructor
  · exact Finset.sum_nonneg fun j _ => (log_step_bound n hn j).1
  · calc
      _ ≤ ∑ _ ∈ Finset.range r, (r : ℝ) / n := by
        apply Finset.sum_le_sum
        intro j hj
        have h : ((j : ℝ) + 1) ≤ r := by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
        exact (log_step_bound n hn j).2.trans (div_le_div_of_nonneg_right h hnR.le)
      _ = _ := by simp [nsmul_eq_mul, pow_two, mul_div_assoc]

noncomputable def oscillation (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I)

noncomputable def factorialPhase (τ : ℝ) (n : Nat) : ℂ :=
  oscillation (τ * Real.log (factorial n))

private theorem oscillation_norm (x : ℝ) : ‖oscillation x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

private theorem oscillation_mul_conj (x y : ℝ) :
    oscillation x * (starRingEnd ℂ) (oscillation y) = oscillation (x - y) := by
  unfold oscillation
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The exact correlation in `lem:logfact` before replacing the block
of logarithms by its asymptotic expression. -/
theorem factorial_phase_correlation (τ : ℝ) (n r : Nat) :
    factorialPhase τ (n + r) * (starRingEnd ℂ) (factorialPhase τ n) =
      oscillation (τ * logBlock n r) := by
  unfold factorialPhase
  rw [oscillation_mul_conj, ← mul_sub, log_factorial_difference]

private theorem norm_oscillation_sub_le (x y : ℝ) :
    ‖oscillation x - oscillation y‖ ≤ 2 * |x - y| := by
  by_cases h : |x - y| ≤ 1
  · have hf : oscillation x - oscillation y =
        oscillation y * (oscillation (x - y) - 1) := by
      rw [mul_sub, mul_one]
      unfold oscillation
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [hf, norm_mul, oscillation_norm, one_mul]
    have hn : ‖(((x - y : ℝ) : ℂ) * Complex.I)‖ = |x - y| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h1 := Complex.norm_exp_sub_one_le (x := (((x - y : ℝ) : ℂ) * Complex.I))
      (by rwa [hn])
    simpa only [oscillation, hn] using h1
  · have hn := norm_sub_le (oscillation x) (oscillation y)
    rw [oscillation_norm, oscillation_norm] at hn
    linarith

/-- The correlation error in `lem:logfact`, with an explicit
constant in the (O_{τ,r}(n^{-1})) term. -/
theorem factorial_correlation_error (τ : ℝ) (n r : Nat) (hn : 0 < n) :
    ‖factorialPhase τ (n + r) * (starRingEnd ℂ) (factorialPhase τ n) -
      oscillation (τ * (r : ℝ) * Real.log n)‖ ≤ 2 * |τ| * ((r : ℝ) ^ 2 / n) := by
  rw [factorial_phase_correlation]
  apply (norm_oscillation_sub_le _ _).trans
  rw [mul_assoc, ← mul_sub, abs_mul]
  obtain ⟨hlo, hhi⟩ := log_block_error n r hn
  rw [abs_of_nonneg hlo, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhi (abs_nonneg τ)) (by norm_num)

/-- The replacement of the correlation by (n^{iτr}) changes its
normalized partial sums by a quantity tending to zero. Indices start
at one, as in `lem:logfact`. -/
theorem factorial_correlation_average_error (τ : ℝ) (r : Nat) :
    Tendsto (fun M : Nat =>
      (M : ℝ)⁻¹ • (∑ j ∈ Finset.range M,
        (factorialPhase τ (j + 1 + r) * (starRingEnd ℂ) (factorialPhase τ (j + 1)))) -
      (M : ℝ)⁻¹ • (∑ j ∈ Finset.range M,
        oscillation (τ * (r : ℝ) * Real.log (j + 1 : Nat)))) atTop (𝓝 0) := by
  let error : Nat → ℂ := fun j =>
    factorialPhase τ (j + 1 + r) * (starRingEnd ℂ) (factorialPhase τ (j + 1)) -
      oscillation (τ * (r : ℝ) * Real.log (j + 1 : Nat))
  have hlimit : Tendsto (fun j : Nat => (2 * |τ| * (r : ℝ) ^ 2) / ((j + 1 : Nat) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).comp (tendsto_add_atTop_nat 1)
  have hpoint : Tendsto error atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    apply squeeze_zero (fun j => norm_nonneg (error j)) _ hlimit
    intro j
    simpa only [error, mul_div_assoc] using factorial_correlation_error τ (j + 1) r (by omega)
  simpa only [error, Finset.sum_sub_distrib, smul_sub] using hpoint.cesaro_smul

/-- The main term (M^{1+ia}/(1+ia)) of the integral comparison,
after dividing by (M). This is continued to (M=0) by the same
explicit expression, which is only used for the limit. -/
noncomputable def normalizedIntegralTerm (a : ℝ) (M : Nat) : ℂ :=
  oscillation (a * Real.log M) / (1 + (a : ℂ) * Complex.I)

theorem norm_normalizedIntegralTerm (a : ℝ) (M : Nat) :
    ‖normalizedIntegralTerm a M‖ = 1 / Real.sqrt (1 + a ^ 2) := by
  rw [normalizedIntegralTerm, norm_div, oscillation_norm]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im, pow_two]

/-- Given the sum–integral comparison stated in `lem:logfact`,
the normalized correlations have the claimed limiting modulus.
The preceding factorial error contributes zero to this limit. -/
theorem factorial_correlation_limit_of_integral_comparison (τ : ℝ) (r : Nat)
    (hIntegral : Tendsto (fun M : Nat =>
      (M : ℝ)⁻¹ • (∑ j ∈ Finset.range M,
        oscillation (τ * (r : ℝ) * Real.log (j + 1 : Nat))) -
      normalizedIntegralTerm (τ * r) M) atTop (𝓝 0)) :
    Tendsto (fun M : Nat =>
      ‖(M : ℝ)⁻¹ • (∑ j ∈ Finset.range M,
        factorialPhase τ (j + 1 + r) * (starRingEnd ℂ) (factorialPhase τ (j + 1)))‖)
      atTop (𝓝 (1 / Real.sqrt (1 + (τ * r) ^ 2))) := by
  let C : Nat → ℂ := fun M => (M : ℝ)⁻¹ • (∑ j ∈ Finset.range M,
    factorialPhase τ (j + 1 + r) * (starRingEnd ℂ) (factorialPhase τ (j + 1)))
  let P := normalizedIntegralTerm (τ * r)
  have h := (factorial_correlation_average_error τ r).add hIntegral
  rw [zero_add] at h
  have hdiff : Tendsto (fun M => C M - P M) atTop (𝓝 0) := by
    refine h.congr (fun M => ?_)
    dsimp only [C, P]
    exact sub_add_sub_cancel _ _ _
  have hn := hdiff.norm
  rw [norm_zero] at hn
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hn ε hε
  refine ⟨K, fun M hM => ?_⟩
  change dist ‖C M‖ (1 / Real.sqrt (1 + (τ * r) ^ 2)) < ε
  rw [← norm_normalizedIntegralTerm (τ * r) M, Real.dist_eq]
  exact (abs_norm_sub_norm_le (C M) (P M)).trans_lt (by simpa [Real.dist_eq] using hK M hM)

end Thesis.FactorialWord
