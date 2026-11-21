import Thesis.StudentOddDegrees

open Real Set Filter Topology MeasureTheory

namespace Thesis.StudyANCOVA

/-- Primitive of (1-y²)^n on the sine coordinate y = sin(arctan(t/√ν)). -/
def evenReduction {K : Type*} [Field K] (y : K) : ℕ → K
  | 0 => y
  | n+1 => ((2*n+2)*evenReduction y n + y*(1-y^2)^(n+1))/(2*n+3)

theorem hasDerivAt_evenReduction (n : ℕ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => evenReduction z n) ((1-y^2)^n) y := by
  induction n with
  | zero => simpa [evenReduction] using hasDerivAt_id y
  | succ n ih =>
    have hp := (((hasDerivAt_pow 2 y).const_sub 1).pow (n+1))
    apply (((ih.const_mul (2*(n:ℝ)+2)).add ((hasDerivAt_id y).mul hp)).div_const (2*n+3)).congr_deriv
    simp only [id_eq, Nat.cast_succ, Nat.add_sub_cancel, Nat.reduceSub, pow_one, pow_succ]
    field_simp
    ring

theorem evenReduction_mono (n : ℕ) : MonotoneOn (fun z : ℝ => evenReduction z n) (Icc (-1) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun x _ => (hasDerivAt_evenReduction n x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_evenReduction n x).differentiableAt.differentiableWithinAt)
  intro x hx
  have hi := interior_subset hx
  change -1 ≤ x ∧ x ≤ 1 at hi
  rw [(hasDerivAt_evenReduction n x).deriv]
  exact pow_nonneg (by nlinarith only [mul_nonneg (sub_nonneg.2 hi.2) (show 0 ≤ 1+x by linarith [hi.1])]) _

theorem ratCast_evenReduction (x : ℚ) (n : ℕ) :
    ((evenReduction x n : ℚ):ℝ) = evenReduction (x:ℝ) n := by
  induction n <;> simp_all [evenReduction]

/-- The exact even-degree Student probability. The recurrence requires only
field arithmetic after the sine coordinate has been enclosed. -/
theorem studentTwoSidedP_even (n : ℕ) {d : ℝ} (hd : 0 < d) (hs : d^2 = 2*n+2) (t : ℝ) :
    studentTwoSidedP (2*n+2) t =
      1-evenReduction (sin (arctan (|t|/d))) n / evenReduction (1:ℝ) n := by
  have hn : 0 < (2*n+2:ℝ) := by positivity
  have hden (k : ℕ) : 0 < evenReduction (1:ℝ) k := by
    induction k with
    | zero => norm_num [evenReduction]
    | succ k ih =>
      simp only [evenReduction,one_pow,sub_self,zero_pow (Nat.succ_ne_zero k),mul_zero,add_zero]
      positivity
  have hz (k : ℕ) : evenReduction (0:ℝ) k = 0 := by induction k <;> simp_all [evenReduction]
  have deriv (x : ℝ) : HasDerivAt (fun y => d * evenReduction (sin (arctan (y/d))) n)
      (studentKernel (2*n+2) x) x := by
    let w := x/d
    have h := ((hasDerivAt_evenReduction n (sin (arctan w))).comp w
      ((hasDerivAt_sin _).comp w (hasDerivAt_arctan w))).comp x ((hasDerivAt_id x).div_const d)
    apply (h.const_mul d).congr_deriv
    have hbase : 0 < 1+w^2 := by positivity
    have hsine : 1-sin (arctan w)^2 = 1/(1+w^2) := by
      rw [sin_arctan, div_pow, sq_sqrt hbase.le]
      field_simp
    have hp : ((2*(n:ℝ)+2)+1)/2 = (n:ℝ)+1+1/2 := by ring
    have he : 1+x^2/(2*(n:ℝ)+2) = 1+w^2 := by dsimp [w]; rw [div_pow,hs]
    simp only [Function.comp_apply, hsine, cos_arctan, studentKernel, he, hp,
      rpow_add hbase, rpow_one, rpow_natCast, ← sqrt_eq_rpow, div_pow, one_pow]
    field_simp
    ring
  have lim := tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop
  have htend : Tendsto (fun x : ℝ => x/d) atTop atTop := tendsto_id.atTop_div_const hd
  have sy : Tendsto (fun x : ℝ => sin (arctan (x/d))) atTop (𝓝 1) := by
    simpa only [sin_pi_div_two] using (continuous_sin.continuousAt.tendsto.comp (lim.comp htend))
  have hl := (((hasDerivAt_evenReduction n 1).continuousAt.tendsto.comp sy).const_mul d)
  have rep (a : ℝ) : studentTail (2*n+2) a =
      d*(evenReduction (1:ℝ) n-evenReduction (sin (arctan (a/d))) n) := by
    have e := integral_Ioi_of_hasDerivAt_of_nonneg' (a := a) (fun x _ => deriv x)
      (fun x _ => (studentKernel_pos hn x).le) hl
    exact e.trans (by ring)
  unfold studentTwoSidedP
  rw [rep,rep,zero_div,arctan_zero,sin_zero,hz,sub_zero]
  field_simp [hd.ne',(hden n).ne']
  ring

end Thesis.StudyANCOVA
