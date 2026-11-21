import Thesis.StudentTails
import Mathlib.Data.Real.Pi.Bounds

open Real Set MeasureTheory Filter Topology

namespace Thesis.StudyANCOVA

/-- The standard reduction for the integral of (1+x²)^(-n-1). Its
initial value is arctan x. Separating that value permits exact rational
enclosures of the reference probabilities at rational endpoints. -/
def studentReduction {K : Type*} [Field K] (x base : K) : ℕ → K
  | 0 => base
  | n+1 => ((2*n+1 : K)/(2*(n+1))) * studentReduction x base n +
    (x/(1+x^2)^(n+1))/(2*(n+1))

theorem hasDerivAt_reduction (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => studentReduction y (arctan y) n) (1/(1+x^2)^(n+1)) x := by
  induction n with
  | zero => simpa [studentReduction] using hasDerivAt_arctan x
  | succ n ih =>
    have hb : 0 < 1+x^2 := by positivity
    have hn : 0 < (n:ℝ)+1 := by positivity
    have hp := (((hasDerivAt_pow 2 x).const_add 1).pow (n+1))
    have hq := ((hasDerivAt_id x).div hp (pow_ne_zero _ hb.ne')).div_const (2*((n:ℝ)+1))
    apply ((ih.const_mul ((2*n+1:ℝ)/(2*(n+1)))).add hq).congr_deriv
    simp only [id_eq, Nat.cast_succ, Nat.add_sub_cancel, Nat.reduceSub, pow_one]
    rw [show n+1+1 = (n+1)+1 by rfl, pow_succ (1+x^2) (n+1), pow_succ (1+x^2) n]
    field_simp
    ring

private theorem tendsto_boundary_zero (n : ℕ) :
    Tendsto (fun x : ℝ => x/(1+x^2)^(n+1)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← one_div, div_le_div_iff₀ (by positivity) hx, one_mul, ← sq]
    exact (by linarith : x^2 ≤ 1+x^2).trans
      (le_self_pow₀ (le_add_of_nonneg_right (sq_nonneg x)) (by omega))

private theorem tendsto_reduction (n : ℕ) :
    Tendsto (fun x : ℝ => studentReduction x (arctan x) n) atTop
      (𝓝 (studentReduction 0 (π/2) n)) := by
  induction n with
  | zero => exact tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop
  | succ n ih =>
    simpa [studentReduction] using
      (ih.const_mul ((2*n+1:ℝ)/(2*(n+1)))).add ((tendsto_boundary_zero n).div_const (2*((n:ℝ)+1)))

private theorem reduction_zero (n : ℕ) : studentReduction (0:ℝ) 0 n = 0 := by
  induction n <;> simp_all [studentReduction]

theorem reduction_mono_base (n : ℕ) (x : ℝ) : Monotone (fun b => studentReduction x b n) := by
  induction n with
  | zero => exact monotone_id
  | succ n ih =>
    intro a b hab
    exact add_le_add_right (mul_le_mul_of_nonneg_left (ih hab) (by positivity)) _

theorem ratCast_reduction (x b : ℚ) (n : ℕ) :
    ((studentReduction x b n : ℚ) : ℝ) = studentReduction (x : ℝ) (b : ℝ) n := by
  induction n <;> simp_all [studentReduction]

/-- Exact two-sided Student probability for an odd number of degrees of
freedom. The scale d is its positive square root. -/
theorem studentTwoSidedP_odd (n : ℕ) {d : ℝ} (hd : 0 < d) (hs : d^2 = 2*n+1) (t : ℝ) :
    studentTwoSidedP (2*n+1) t =
      1 - studentReduction (|t|/d) (arctan (|t|/d)) n / studentReduction 0 (π/2) n := by
  have hν : 0 < (2*n+1:ℝ) := by positivity
  have masspos (k : ℕ) : 0 < studentReduction (0:ℝ) (π/2) k := by
    induction k with
    | zero => exact half_pos pi_pos
    | succ k ih =>
      simp only [studentReduction, zero_div, add_zero]
      positivity
  have htend : Tendsto (fun x : ℝ => x/d) atTop atTop :=
    tendsto_id.atTop_div_const hd
  have rep (a : ℝ) : studentTail (2*n+1) a =
      d * (studentReduction 0 (π/2) n - studentReduction (a/d) (arctan (a/d)) n) := by
    have deriv (x : ℝ) : HasDerivAt (fun y => d * studentReduction (y/d) (arctan (y/d)) n)
        (studentKernel (2*n+1) x) x := by
      apply (((hasDerivAt_reduction n (x/d)).comp x ((hasDerivAt_id x).div_const d)).const_mul d).congr_deriv
      have exp_eq : ((2*n+1:ℝ)+1)/2 = ((n+1:ℕ):ℝ) := by push_cast; ring
      rw [studentKernel, exp_eq, rpow_natCast, div_pow, hs]
      field_simp
      ring
    have lim := ((tendsto_reduction n).comp htend).const_mul d
    have he := integral_Ioi_of_hasDerivAt_of_nonneg' (a := a) (fun x _ => deriv x)
      (fun x _ => (studentKernel_pos hν x).le) lim
    exact he.trans (by ring)
  unfold studentTwoSidedP
  rw [rep, rep, zero_div, arctan_zero, reduction_zero, sub_zero]
  field_simp [hd.ne', (masspos n).ne']
  ring

/-- The first two alternating polynomial bounds for arctan on the positive
axis. Only small arguments are needed for the ANCOVA table. -/
theorem arctan_cubic_quintic {x : ℝ} (hx : 0 ≤ x) :
    x-x^3/3 ≤ arctan x ∧ arctan x ≤ x-x^3/3+x^5/5 := by
  have hl (y : ℝ) : HasDerivAt (fun z => arctan z - (z-z^3/3))
      (1/(1+y^2)-(1-y^2)) y := by
    apply ((hasDerivAt_arctan y).sub ((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 3))).congr_deriv
    norm_num
  have hu (y : ℝ) : HasDerivAt (fun z => (z-z^3/3+z^5/5) - arctan z)
      ((1-y^2+y^4)-1/(1+y^2)) y := by
    apply ((((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 3)).add
      ((hasDerivAt_pow 5 y).div_const 5)).sub (hasDerivAt_arctan y)).congr_deriv
    norm_num
  have low := monotone_of_deriv_nonneg (fun y => (hl y).differentiableAt) (fun y => by
    rw [(hl y).deriv, sub_nonneg, le_div_iff₀ (by positivity)]
    nlinarith only [sq_nonneg (y^2)])
  have up := monotone_of_deriv_nonneg (fun y => (hu y).differentiableAt) (fun y => by
    rw [(hu y).deriv, sub_nonneg, div_le_iff₀ (by positivity)]
    nlinarith only [sq_nonneg (y^3)])
  have h₁ := low hx
  have h₂ := up hx
  simp only [arctan_zero, zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 5 ≠ 0),
    zero_div, sub_zero, add_zero, sub_self] at h₁ h₂
  exact ⟨by linarith, by linarith⟩

end Thesis.StudyANCOVA
