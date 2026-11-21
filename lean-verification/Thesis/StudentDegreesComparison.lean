import Thesis.StudentTails

open Real Set MeasureTheory intervalIntegral

namespace Thesis.StudyANCOVA

private noncomputable def logKernel (v x : ℝ) := -((v+1)/2) * log (1+x^2/v)

private theorem exp_logKernel {v : ℝ} (hv : 0 < v) (x : ℝ) : exp (logKernel v x) = studentKernel v x := by
  unfold logKernel studentKernel
  rw [Real.rpow_def_of_pos (by positivity), one_div, ← exp_neg]
  congr 1
  ring

private theorem kernel_log_deriv_x {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasDerivAt (logKernel v) (-((v+1)*x)/(v+x^2)) x := by
  have h := ((((hasDerivAt_pow 2 x).div_const v).const_add 1).log (by positivity)).const_mul (-((v+1)/2))
  apply h.congr_deriv
  field_simp
  ring

private theorem kernel_log_deriv_v {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasDerivAt (fun w => logKernel w x)
      (-(log (1+x^2/v))/2 + (v+1)*x^2/(2*v*(v+x^2))) v := by
  have hl := ((((hasDerivAt_const v (x^2)).div (hasDerivAt_id v) hv.ne').const_add 1).log
    (show 1+x^2/v ≠ 0 by positivity))
  apply (((((hasDerivAt_id v).add_const 1).div_const 2).neg).mul hl).congr_deriv
  simp only [id_eq]
  field_simp
  ring

private theorem logKernel_decreases_degrees {t : ℝ} (ht : 1.5 ≤ t) :
    AntitoneOn (fun v => logKernel v t) (Ici (79:ℝ)) := by
  have hv (v : ℝ) (h : v ∈ Ici (79:ℝ)) : 0 < v := lt_of_lt_of_le (by norm_num) h
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    (fun v h => (kernel_log_deriv_v (hv v h) t).continuousAt.continuousWithinAt)
    (fun v h => (kernel_log_deriv_v (hv v (interior_subset h)) t).differentiableAt.differentiableWithinAt)
  intro v hv'
  have h79 : 79 ≤ v := interior_subset hv'
  have hv := hv v h79
  rw [(kernel_log_deriv_v hv t).deriv]
  have lower := Real.le_log_one_add_of_nonneg (show 0 ≤ t^2/v by positivity)
  have hs : (v+1)*t^2/(v*(v+t^2)) ≤ 2*(t^2/v)/(t^2/v+2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    field_simp
    have h₁ := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1.5) ht 2
    have hp := mul_nonneg (show 0 ≤ v-1 by linarith) (show 0 ≤ t^2-2.25 by linarith)
    have hcond : 0 ≤ (v-1)*t^2-2*v := by linarith only [hp,h79]
    apply div_le_div_of_nonneg_right _ hv.le
    nlinarith only [mul_nonneg (sq_nonneg t) hcond]
  have he : (v+1)*t^2/(2*v*(v+t^2)) = ((v+1)*t^2/(v*(v+t^2)))/2 := by field_simp; ring
  rw [he]
  linarith only [hs,lower]

private theorem logRatio_order {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MonotoneOn (fun x => logKernel b x-logKernel a x) (Icc 0 1) ∧
    AntitoneOn (fun x => logKernel b x-logKernel a x) (Ici 1) := by
  have hb := ha.trans_le hab
  have deriv (x : ℝ) : HasDerivAt (fun x => logKernel b x-logKernel a x)
      (x*(b-a)*(1-x^2)/((a+x^2)*(b+x^2))) x := by
    apply ((kernel_log_deriv_x hb x).sub (kernel_log_deriv_x ha x)).congr_deriv
    field_simp
    ring
  constructor
  · apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (fun x _ => (deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (deriv x).differentiableAt.differentiableWithinAt)
    intro x hx
    obtain ⟨hl,hu⟩ := (interior_subset hx : x ∈ Icc (0:ℝ) 1)
    rw [(deriv x).deriv]
    have hq : 0 ≤ 1-x^2 := by linarith only [pow_le_pow_left₀ hl hu 2]
    exact div_nonneg (mul_nonneg (mul_nonneg hl (sub_nonneg.2 hab)) hq) (by positivity)
  · apply antitoneOn_of_deriv_nonpos (convex_Ici _) (fun x _ => (deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (deriv x).differentiableAt.differentiableWithinAt)
    intro x hx
    have hl : 1 ≤ x := interior_subset hx
    rw [(deriv x).deriv]
    have hq := pow_le_pow_left₀ zero_le_one hl 2
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) (sub_nonneg.2 hab)) (by linarith)) (by positivity)

theorem integrable_studentKernel {v : ℝ} (hv : 1 ≤ v) : Integrable (studentKernel v) := by
  have hv' : 0 < v := zero_lt_one.trans_le hv
  apply (integrable_inv_one_add_sq.const_mul v).mono' (continuous_studentKernel hv').aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (studentKernel_pos hv' _), studentKernel]
  have hbase : 1 ≤ 1+x^2/v := le_add_of_nonneg_right (by positivity)
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase (by linarith : (1:ℝ) ≤ (v+1)/2)
  rw [rpow_one] at hpow
  apply (one_div_le_one_div_of_le (by positivity) hpow).trans
  rw [← div_eq_mul_inv, one_div_le (by positivity) (by positivity)]
  field_simp
  exact div_le_div_of_nonneg_right (by linarith) hv'.le

theorem studentTail_split_of_one_le {v s t : ℝ} (hv : 1 ≤ v) (hst : s ≤ t) :
    studentTail v s = (∫ x in s..t, studentKernel v x) + studentTail v t := by
  have hint := integrable_studentKernel hv
  unfold studentTail
  rw [intervalIntegral.integral_of_le hst, ← Ioc_union_Ioi_eq_Ioi hst]
  exact setIntegral_union (disjoint_left.2 (fun _ hx hy => (not_lt_of_ge hx.2) hy))
    measurableSet_Ioi hint.integrableOn hint.integrableOn

theorem studentProbability_strictAnti {v : ℝ} (hv : 1 ≤ v) : StrictAntiOn (studentTwoSidedP v) (Ici 0) := by
  have hv' := zero_lt_one.trans_le hv
  have anti : StrictAnti (studentTail v) := by
    intro s t h
    rw [studentTail_split_of_one_le hv h.le]
    exact lt_add_of_pos_left _ (intervalIntegral_pos_of_pos
      ((continuous_studentKernel hv').intervalIntegrable _ _) (studentKernel_pos hv') h)
  have h0 := (studentTail_nonneg hv' 1).trans_lt (anti (zero_lt_one : (0:ℝ)<1))
  intro s hs t ht hst
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  simp only [studentTwoSidedP, abs_of_nonneg hs, abs_of_nonneg ht]
  exact div_lt_div_of_pos_right (anti hst) h0

theorem continuous_studentProbability {v : ℝ} (hv : 1 ≤ v) : Continuous (studentTwoSidedP v) := by
  have he : studentTwoSidedP v = fun t => (studentTail v 0 - intervalIntegral (studentKernel v) 0 (abs t) volume)/studentTail v 0 := by
    funext t
    unfold studentTwoSidedP
    congr 1
    linarith only [studentTail_split_of_one_le hv (abs_nonneg t)]
  rw [he]
  have hc := continuous_studentKernel (zero_lt_one.trans_le hv)
  apply Continuous.div_const
  apply continuous_const.sub
  exact (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).comp continuous_abs

/-- If the same constant bounds the density ratio from below on the
central interval and from above on the tail, normalization preserves the
tail comparison. Both Student comparisons use this argument. -/
theorem normalized_tail_compare {f g : ℝ → ℝ} {k t : ℝ} (ht : 0 < t)
    (hf : Integrable f) (hg : Integrable g) (fc : Continuous f) (gc : Continuous g)
    (fp : ∀ x, 0 < f x) (gp : ∀ x, 0 < g x)
    (central : ∀ x ∈ Icc 0 t, k*f x ≤ g x) (tail : ∀ x ∈ Ioi t, g x ≤ k*f x) :
    (∫ x in Ioi t, g x)/(∫ x in Ioi 0, g x) ≤ (∫ x in Ioi t, f x)/(∫ x in Ioi 0, f x) := by
  let C (w : ℝ → ℝ) := ∫ x in Ioc 0 t, w x
  let T (w : ℝ → ℝ) := ∫ x in Ioi t, w x
  have hT : T g ≤ k*T f := by
    simpa only [T,MeasureTheory.integral_const_mul] using
      setIntegral_mono_on hg.integrableOn (hf.const_mul k).integrableOn measurableSet_Ioi tail
  have hC : k*C f ≤ C g := by
    simpa only [C,MeasureTheory.integral_const_mul] using setIntegral_mono_on
      (hf.const_mul k).integrableOn hg.integrableOn measurableSet_Ioc (fun x hx => central x ⟨hx.1.le,hx.2⟩)
  have split (w : ℝ → ℝ) (hw : Integrable w) : (∫ x in Ioi 0, w x) = C w + T w := by
    rw [← Ioc_union_Ioi_eq_Ioi ht.le]
    exact setIntegral_union (disjoint_left.2 (fun _ hx hy => (not_lt_of_ge hx.2) hy)) measurableSet_Ioi
      hw.integrableOn hw.integrableOn
  have pos (w : ℝ → ℝ) (wc : Continuous w) (wp : ∀ x, 0 < w x) : 0 < C w := by
    dsimp [C]
    rw [← intervalIntegral.integral_of_le ht.le]
    exact intervalIntegral_pos_of_pos (wc.intervalIntegrable _ _) wp ht
  have cf := pos f fc fp
  have cg := pos g gc gp
  have tf : 0 ≤ T f := integral_nonneg (fun x => (fp x).le)
  have tg : 0 ≤ T g := integral_nonneg (fun x => (gp x).le)
  rw [split f hf,split g hg]
  change T g/(C g+T g) ≤ T f/(C f+T f)
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  have prod : T g*C f ≤ T f*C g := calc
    _ ≤ (k*T f)*C f := mul_le_mul_of_nonneg_right hT cf.le
    _ = T f*(k*C f) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hC tf
  linarith only [prod]


/-- For the Welch tests in §4.3, an odd integer on either side of the real
Welch degrees of freedom gives a rigorous bound for the two-sided p value.
On the central interval the density ratio is at least its value at t, and
on the tail it is at most that value. -/
theorem student_probability_antitone_degrees {a b t : ℝ} (ha : 79 ≤ a) (hab : a ≤ b) (ht : 1.5 ≤ t) :
    studentTwoSidedP b t ≤ studentTwoSidedP a t := by
  have ha' : 0 < a := by linarith
  have hb' := ha'.trans_le hab
  have ht' : 0 ≤ t := by linarith
  let R := fun x => logKernel b x-logKernel a x
  let k := exp (R t)
  have hk : 0 ≤ k := (exp_pos _).le
  obtain ⟨mono,anti⟩ := logRatio_order ha' hab
  have hneg : R t ≤ R 0 := by
    have h := logKernel_decreases_degrees ht ha (ha.trans hab) hab
    simp only [R, logKernel, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero, log_one, mul_zero, sub_zero]
    exact sub_nonpos.2 h
  have he (x : ℝ) : exp (R x) = studentKernel b x / studentKernel a x := by
    simp only [R, Real.exp_sub, exp_logKernel ha', exp_logKernel hb']
  have central (x : ℝ) (hx : x ∈ Icc 0 t) : k*studentKernel a x ≤ studentKernel b x := by
    have h : R t ≤ R x := by
      by_cases h1 : x ≤ 1
      · exact hneg.trans (mono ⟨le_rfl,zero_le_one⟩ ⟨hx.1,h1⟩ hx.1)
      · exact anti (le_of_not_ge h1) (by change 1 ≤ t; linarith) hx.2
    exact (le_div_iff₀ (studentKernel_pos ha' _)).1 ((he x) ▸ exp_le_exp.2 h)
  have tail (x : ℝ) (hx : x ∈ Ioi t) : studentKernel b x ≤ k*studentKernel a x := by
    have h : R x ≤ R t := anti (by change 1 ≤ t; linarith) (by change 1 ≤ x; linarith [hx.out]) hx.le
    exact (div_le_iff₀ (studentKernel_pos ha' _)).1 ((he x) ▸ exp_le_exp.2 h)
  simp only [studentTwoSidedP,abs_of_nonneg ht',studentTail]
  exact normalized_tail_compare (by linarith) (integrable_studentKernel (by linarith))
    (integrable_studentKernel (by linarith)) (continuous_studentKernel ha') (continuous_studentKernel hb')
    (studentKernel_pos ha') (studentKernel_pos hb') central tail

end Thesis.StudyANCOVA
