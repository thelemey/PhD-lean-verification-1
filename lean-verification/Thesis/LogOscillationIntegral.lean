import Thesis.FactorialCorrelations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Topology Set intervalIntegral
open scoped BigOperators Interval

namespace Thesis.FactorialWord

/-- The function (x^{ia}) on the positive real axis. -/
noncomputable def logOscillation (a x : ℝ) : ℂ :=
  oscillation (a * Real.log x)

/-- The antiderivative (x^{1+ia}/(1+ia)) used in the thesis. -/
noncomputable def oscillationPrimitive (a x : ℝ) : ℂ :=
  (x : ℂ) * logOscillation a x / (1 + (a : ℂ) * Complex.I)

private noncomputable def oscillationDerivative (a x : ℝ) : ℂ :=
  logOscillation a x * (((a / x : ℝ) : ℂ) * Complex.I)

private theorem logOscillation_hasDerivAt (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logOscillation a) (oscillationDerivative a x) x := by
  have hd := ((Real.hasDerivAt_log hx.ne').const_mul a).ofReal_comp
  have he := (hd.mul_const Complex.I).cexp
  simpa only [oscillationDerivative, logOscillation, oscillation, div_eq_mul_inv] using he

private theorem logOscillation_norm (a x : ℝ) : ‖logOscillation a x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem oscillationDerivative_norm (a : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖oscillationDerivative a x‖ = |a| * x⁻¹ := by
  rw [oscillationDerivative, norm_mul, logOscillation_norm, one_mul,
    norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_div, abs_of_pos hx, div_eq_mul_inv]

private theorem oscillationPrimitive_hasDerivAt (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (oscillationPrimitive a) (logOscillation a x) x := by
  have hd := (hasDerivAt_id x).ofReal_comp
  have he := (hd.mul (logOscillation_hasDerivAt a hx)).div_const (1 + (a : ℂ) * Complex.I)
  convert he using 1
  simp only [oscillationDerivative, Complex.ofReal_div, Complex.ofReal_one, one_mul,
    id_eq]
  have hden : (1 + (a : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp [Complex.mul_re] at he
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  apply (eq_div_iff hden).2
  field_simp [hx']
  ring

private theorem model_continuousOn_pos (a : ℝ) : ContinuousOn (logOscillation a) (Ioi 0) :=
  fun _ hx => (logOscillation_hasDerivAt a hx).continuousAt.continuousWithinAt

private theorem deriv_continuousOn_pos (a : ℝ) : ContinuousOn (oscillationDerivative a) (Ioi 0) := by
  unfold oscillationDerivative
  apply (model_continuousOn_pos a).mul
  exact (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_const.div continuous_id.continuousOn (fun _ hx => ne_of_gt hx))).mul
      continuousOn_const

private theorem interval_subset_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    uIcc x y ⊆ Ioi 0 := by
  rw [uIcc_of_le hxy]
  exact fun _ hz => hx.trans_le hz.1

private theorem integral_logOscillation (a : ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (∫ t in x..y, logOscillation a t) = oscillationPrimitive a y - oscillationPrimitive a x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · exact fun _ hz => oscillationPrimitive_hasDerivAt a (interval_subset_pos hx hxy hz)
  · exact ((model_continuousOn_pos a).mono (interval_subset_pos hx hxy)).intervalIntegrable

private theorem logOscillation_increment_bound (a : ℝ) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    ‖logOscillation a y - logOscillation a x‖ ≤ |a| * (Real.log y - Real.log x) := by
  have hpos := interval_subset_pos hx hxy
  have hint : IntervalIntegrable (oscillationDerivative a) MeasureTheory.volume x y :=
    ((deriv_continuousOn_pos a).mono hpos).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun _ hz => logOscillation_hasDerivAt a (hpos hz)) hint
  rw [← hFTC]
  apply (intervalIntegral.norm_integral_le_integral_norm hxy).trans_eq
  have hcong : (∫ t in x..y, ‖oscillationDerivative a t‖) = ∫ t in x..y, |a| * t⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact oscillationDerivative_norm a (hpos ht)
  rw [hcong, intervalIntegral.integral_const_mul]
  have hl : (∫ t : ℝ in x..y, t⁻¹) = Real.log y - Real.log x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · exact fun _ hz => Real.hasDerivAt_log (hpos hz).ne'
    · have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Ioi 0) :=
        continuous_id.continuousOn.inv₀ (fun _ ht => ne_of_gt ht)
      exact (hcont.mono hpos).intervalIntegrable
  rw [hl]

private theorem interval_step_error (a : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖logOscillation a x - (oscillationPrimitive a (x + 1) - oscillationPrimitive a x)‖ ≤
      |a| * (Real.log (x + 1) - Real.log x) := by
  have hxy : x ≤ x + 1 := by linarith
  have hi : IntervalIntegrable (logOscillation a) MeasureTheory.volume x (x + 1) :=
    ((model_continuousOn_pos a).mono (interval_subset_pos hx hxy)).intervalIntegrable
  have hc : (∫ _ : ℝ in x..(x + 1), logOscillation a x) = logOscillation a x := by
    rw [intervalIntegral.integral_const, add_sub_cancel_left, one_smul]
  rw [← integral_logOscillation a hx hxy, ← hc, ← intervalIntegral.integral_sub intervalIntegrable_const hi]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := x) (b := x + 1) (C := |a| * (Real.log (x + 1) - Real.log x))
    (f := fun t => logOscillation a x - logOscillation a t) (by
      intro t ht
      rw [uIoc_of_le hxy] at ht
      have h1 : x ≤ t := ht.1.le
      have h2 : t ≤ x + 1 := ht.2
      rw [norm_sub_rev]
      apply (logOscillation_increment_bound a hx h1).trans
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right
        (Real.log_le_log (hx.trans_le h1) h2) _) (abs_nonneg a))
  simpa only [add_sub_cancel_left, abs_one, mul_one] using hb

private theorem sum_integral_error_through (a : ℝ) (M : Nat) :
    ‖(∑ j ∈ Finset.range M, logOscillation a ((j : ℝ) + 1)) -
        (oscillationPrimitive a ((M : ℝ) + 1) - oscillationPrimitive a 1)‖ ≤
      |a| * Real.log ((M : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h := interval_step_error a (x := (M : ℝ) + 1) (by positivity)
    rw [Finset.sum_range_succ, Nat.cast_succ]
    rw [show
      (∑ j ∈ Finset.range M, logOscillation a ((j : ℝ) + 1)) +
          logOscillation a ((M : ℝ) + 1) -
        (oscillationPrimitive a ((M : ℝ) + 1 + 1) - oscillationPrimitive a 1) =
      ((∑ j ∈ Finset.range M, logOscillation a ((j : ℝ) + 1)) -
        (oscillationPrimitive a ((M : ℝ) + 1) - oscillationPrimitive a 1)) +
      (logOscillation a ((M : ℝ) + 1) -
        (oscillationPrimitive a ((M : ℝ) + 1 + 1) -
          oscillationPrimitive a ((M : ℝ) + 1))) by ring]
    exact (norm_add_le _ _).trans ((add_le_add ih h).trans_eq (by ring))

/-- The sum–integral error of `lem:logfact`, including the last term
at (M). This is the displayed estimate (1+|a|\log M). -/
theorem log_oscillation_sum_integral_error (a : ℝ) {M : Nat} (hM : 0 < M) :
    ‖(∑ j ∈ Finset.range M, logOscillation a ((j : ℝ) + 1)) -
      (∫ x in (1 : ℝ)..(M : ℝ), logOscillation a x)‖ ≤
      1 + |a| * Real.log (M : ℝ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  rw [integral_logOscillation a zero_lt_one (by norm_cast),
    Finset.sum_range_succ, Nat.cast_succ]
  rw [show
    (∑ i ∈ Finset.range j, logOscillation a ((i : ℝ) + 1)) +
      logOscillation a ((j : ℝ) + 1) -
        (oscillationPrimitive a ((j : ℝ) + 1) - oscillationPrimitive a 1) =
    logOscillation a ((j : ℝ) + 1) + ((∑ i ∈ Finset.range j, logOscillation a ((i : ℝ) + 1)) -
      (oscillationPrimitive a ((j : ℝ) + 1) - oscillationPrimitive a 1)) by ring]
  exact (norm_add_le _ _).trans (add_le_add (logOscillation_norm _ _).le
    (sum_integral_error_through a j))

private theorem norm_primitive_one_le (a : ℝ) : ‖oscillationPrimitive a 1‖ ≤ 1 := by
  rw [oscillationPrimitive, Complex.ofReal_one, one_mul, norm_div, logOscillation_norm]
  have he : ‖(1 + (a : ℂ) * Complex.I)‖ = Real.sqrt (1 + a ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [he]
  exact div_le_one_of_le₀ (by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + a ^ 2 by linarith [sq_nonneg a]))
    (Real.sqrt_nonneg _)

/-- The normalized form of the sum–integral comparison used by the
factorial correlation limit. -/
theorem log_oscillation_normalized_error (a : ℝ) :
    Tendsto (fun M : Nat => (M : ℝ)⁻¹ •
      (∑ j ∈ Finset.range M, logOscillation a ((j : ℝ) + 1)) -
      normalizedIntegralTerm a M) atTop (𝓝 0) := by
  have hlog : Tendsto (fun M : Nat => Real.log (M : ℝ) / M) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun M : Nat => 2 / (M : ℝ) + |a| * (Real.log (M : ℝ) / M))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat 2).add (hlog.const_mul |a|)
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hM0 : 0 < M := by omega
  have hp : (0 : ℝ) < M := by exact_mod_cast hM0
  have hscaled : (M : ℝ)⁻¹ • oscillationPrimitive a (M : ℝ) = normalizedIntegralTerm a M := by
    rw [oscillationPrimitive, normalizedIntegralTerm, Complex.real_smul, ← mul_div_assoc,
      ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hp.ne', Complex.ofReal_one, one_mul]
    rfl
  rw [← hscaled, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hp.le)]
  have he := log_oscillation_sum_integral_error a hM0
  rw [integral_logOscillation a zero_lt_one (by exact_mod_cast hM)] at he
  have hbd : ‖(∑ j ∈ Finset.range M, logOscillation a ((j : ℝ) + 1)) -
      oscillationPrimitive a (M : ℝ)‖ ≤ 2 + |a| * Real.log (M : ℝ) := by
    rw [show (∑ j ∈ Finset.range M, logOscillation a ((j : ℝ) + 1)) -
        oscillationPrimitive a (M : ℝ) =
        ((∑ j ∈ Finset.range M, logOscillation a ((j : ℝ) + 1)) -
          (oscillationPrimitive a (M : ℝ) - oscillationPrimitive a 1)) -
        oscillationPrimitive a 1 by ring]
    exact (norm_sub_le _ _).trans ((add_le_add he (norm_primitive_one_le a)).trans_eq (by ring))
  exact (mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hp.le)).trans_eq (by ring)

end Thesis.FactorialWord
