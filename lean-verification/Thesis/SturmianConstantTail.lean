import Thesis.SturmianDensityDichotomy
import Mathlib.Data.Real.GoldenRatio

open Filter Topology

namespace Thesis.SturmianDensity

/-- The positive root of (t² + a t - 1 = 0) in `cor:palSturm`. -/
noncomputable def constantTailRoot (a : Nat) : ℝ :=
  (Real.sqrt ((a : ℝ) ^ 2 + 4) - a) / 2

private theorem constantTailRoot_sq (a : Nat) :
    constantTailRoot a ^ 2 + (a : ℝ) * constantTailRoot a = 1 := by
  have h := Real.sq_sqrt (by positivity : 0 ≤ (a : ℝ) ^ 2 + 4)
  unfold constantTailRoot
  nlinarith

private theorem constantTailRoot_pos (a : Nat) : 0 < constantTailRoot a := by
  have hs := Real.sqrt_nonneg ((a : ℝ) ^ 2 + 4)
  have ha : (0 : ℝ) ≤ a := by positivity
  have h := Real.sq_sqrt (by positivity : 0 ≤ (a : ℝ) ^ 2 + 4)
  have hl : (a : ℝ) < Real.sqrt ((a : ℝ) ^ 2 + 4) := by
    by_contra! hh
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (add_nonneg ha hs)]
  unfold constantTailRoot
  linarith

private theorem constantTailRoot_lt_one {a : Nat} (ha : 0 < a) : constantTailRoot a < 1 := by
  have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have h := constantTailRoot_sq a
  have ht := constantTailRoot_pos a
  by_contra! hn
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) ht.le, sq_nonneg (constantTailRoot a)]

private theorem tail_distance_step (s : ReversedFractions) (a k : Nat) (ha : 0 < a)
    (hk : s.a k = a) :
    |s.t (k + 1) - constantTailRoot a| ≤ constantTailRoot a * |s.t k - constantTailRoot a| := by
  let r := constantTailRoot a
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hden : (1 : ℝ) ≤ (a : ℝ) + s.t k := by linarith [(s.t_bounds k).1]
  have hp : 0 < (a : ℝ) + s.t k := zero_lt_one.trans_le hden
  have hr := constantTailRoot_pos a
  have hsq := constantTailRoot_sq a
  have he : s.t (k + 1) - r = r * (r - s.t k) / ((a : ℝ) + s.t k) := by
    rw [s.step, hk]
    field_simp [hp.ne']
    dsimp [r]
    nlinarith only [hsq]
  change |s.t (k + 1) - r| ≤ r * |s.t k - r|
  rw [he, abs_div, abs_mul, abs_of_pos hp, abs_of_pos hr, abs_sub_comm r]
  apply div_le_self (mul_nonneg hr.le (abs_nonneg _)) hden

/-- The reversed fractions tend to [0;a,a,…] when the partial quotients
are eventually equal to a, as used in `cor:palSturm`. -/
theorem reversed_fraction_constant_tail (s : ReversedFractions) (a k₀ : Nat)
    (h : ∀ k ≥ k₀, s.a k = a) :
    Tendsto s.t atTop (𝓝 (constantTailRoot a)) := by
  have ha : 0 < a := h k₀ le_rfl ▸ s.a_pos k₀
  let r := constantTailRoot a
  have hr := constantTailRoot_pos a
  have hbound (n : Nat) : |s.t (n + k₀) - r| ≤ r ^ n * |s.t k₀ - r| := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show n + 1 + k₀ = n + k₀ + 1 by omega]
      calc
        |s.t (n + k₀ + 1) - r| ≤ r * |s.t (n + k₀) - r| :=
          tail_distance_step s a (n + k₀) ha (h _ (by omega))
        _ ≤ r * (r ^ n * |s.t k₀ - r|) := mul_le_mul_of_nonneg_left ih hr.le
        _ = r ^ (n + 1) * |s.t k₀ - r| := by rw [pow_succ]; ring
  apply (tendsto_add_atTop_iff_nat k₀).mp
  apply tendsto_iff_dist_tendsto_zero.2
  simp only [Real.dist_eq]
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le
    (constantTailRoot_lt_one ha)).mul_const |s.t k₀ - r|
  rw [zero_mul] at hlim
  exact squeeze_zero (fun _ => abs_nonneg _) hbound hlim

private theorem density_of_tail_limit (s : ReversedFractions) {r : ℝ} (hr : 0 ≤ r)
    (h : Tendsto s.t atTop (𝓝 r)) :
    s.fischlerDensity = (1 + r) / (2 + r) := by
  have hd : (1 : ℝ) + r ≠ 0 := by positivity
  have ht : Tendsto s.peak atTop (𝓝 (1 + 1 / (1 + r))) := by
    change Tendsto (fun k => 1 + 1 / (1 + s.t (k + 1))) atTop _
    simpa only [one_div, Function.comp_apply] using
      (((h.comp (tendsto_add_atTop_nat 1)).const_add 1).inv₀ hd).const_add 1
  rw [ReversedFractions.fischlerDensity, ht.limsup_eq]
  have hp : (2 : ℝ) + r ≠ 0 := by positivity
  field_simp [hd, hp]
  ring

/-- The explicit density from `cor:palSturm` for an eventually constant
sequence of partial quotients, via the cited Fischler formula. -/
theorem density_constant_tail (s : ReversedFractions) (a k₀ : Nat)
    (h : ∀ k ≥ k₀, s.a k = a) :
    s.fischlerDensity = (1 + constantTailRoot a) / (2 + constantTailRoot a) :=
  density_of_tail_limit s (constantTailRoot_pos a).le (reversed_fraction_constant_tail s a k₀ h)

/-- The eventual all-ones value in `cor:palSturm`. -/
theorem density_ones_tail (s : ReversedFractions) (k₀ : Nat) (h : ∀ k ≥ k₀, s.a k = 1) :
    s.fischlerDensity = 1 / goldenRatio := by
  rw [density_constant_tail s 1 k₀ h]
  have hp := constantTailRoot_pos 1
  have hs := constantTailRoot_sq 1
  norm_num at hs
  have he : goldenRatio = 1 + constantTailRoot 1 := by
    norm_num [goldenRatio, constantTailRoot]
    ring
  rw [he]
  have h2 : (2 : ℝ) + constantTailRoot 1 ≠ 0 := by positivity
  have h1 : (1 : ℝ) + constantTailRoot 1 ≠ 0 := by positivity
  field_simp [h1, h2]
  nlinarith only [hs]

/-- The eventual all-twos value in `cor:palSturm`. -/
theorem density_twos_tail (s : ReversedFractions) (k₀ : Nat) (h : ∀ k ≥ k₀, s.a k = 2) :
    s.fischlerDensity = 2 - Real.sqrt 2 := by
  rw [density_constant_tail s 2 k₀ h]
  have he : constantTailRoot 2 = Real.sqrt 2 - 1 := by
    have hs : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
      have hs4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : Nat) by norm_num, Real.sqrt_sq (by norm_num)]
      rw [hs4]
    norm_num [constantTailRoot, hs]
    ring
  rw [he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hn : (2 : ℝ) + (Real.sqrt 2 - 1) ≠ 0 := by linarith
  field_simp [hn]
  nlinarith only [hs]

private theorem roots_tendsto_zero : Tendsto constantTailRoot atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun a => (constantTailRoot_pos a).le) _
    tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with a ha
  have ha' : 0 < a := by omega
  have hp : (0 : ℝ) < a := by exact_mod_cast ha'
  have hs := constantTailRoot_sq a
  exact (le_div_iff₀ hp).2 (by nlinarith [sq_nonneg (constantTailRoot a)])

/-- The eventual-constant density values tend to one half. -/
theorem constant_tail_values_tendsto_half :
    Tendsto (fun a => (1 + constantTailRoot a) / (2 + constantTailRoot a))
      atTop (𝓝 ((1 : ℝ) / 2)) := by
  simpa only [add_zero] using
    (roots_tendsto_zero.const_add 1).div (roots_tendsto_zero.const_add 2) (by norm_num)

/-- The explicit eventual-constant density decreases strictly with the
constant partial quotient, as stated in `cor:palSturm`. -/
theorem constant_tail_values_strictAnti :
    StrictAnti (fun a => (1 + constantTailRoot a) / (2 + constantTailRoot a)) := by
  intro a b hab
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have ha := constantTailRoot_pos a
  have hb := constantTailRoot_pos b
  have hroot : constantTailRoot b < constantTailRoot a := by
    by_contra! hle
    have hsq := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg ha.le hb.le)
    have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) b) (sub_nonneg.mpr hle)
    have hstrict := mul_pos (sub_pos.mpr hab') ha
    nlinarith [constantTailRoot_sq a, constantTailRoot_sq b]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  linarith

end Thesis.SturmianDensity
