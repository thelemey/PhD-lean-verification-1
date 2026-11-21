import Thesis.ThinkingGainComparison

open Finset Real Set

namespace Thesis.StudyANCOVA

abbrev PilotScores := Fin 40 → ℤ
def pilotColumn (x : PilotScores) : Fin 40 → ℝ := fun i => x i
noncomputable def pilotT (z : Fin 40 → ℝ) := mean z * sqrt 40 / sqrt (ss z/39)

/-- The 40-pupil pilot was separate from the two 42-pupil classes. Its
integer scores and the two printed means fix the mean shift exactly. The
paired t supplies the sum of squared differences. -/
theorem pilot_integer_shift (x y : PilotScores)
    (hx : RoundsTo (mean (pilotColumn x)) 8.15) (hy : RoundsTo (mean (pilotColumn y)) 9.18)
    (ht : RoundsTo (pilotT (fun i => pilotColumn y i-pilotColumn x i)) 4.29) :
    (∑ i, x i) = 326 ∧ (∑ i, y i) = 367 ∧
    (∑ i, (y i-x i)^2) = 131 ∧ mean (fun i => pilotColumn y i-pilotColumn x i) = 41/40 ∧
    ss (fun i => pilotColumn y i-pilotColumn x i) = 3559/40 := by
  have avg (w : PilotScores) : mean (pilotColumn w) = ((∑ i, w i : ℤ):ℝ)/40 := by simp [mean,pilotColumn]
  rw [avg] at hx hy
  obtain ⟨xl,xu⟩ := abs_le.mp hx
  obtain ⟨yl,yu⟩ := abs_le.mp hy
  have sx : ∑ i, x i = 326 := by
    have l : (325:ℤ) < ∑ i,x i := by exact_mod_cast (show (325:ℝ) < ((∑ i,x i : ℤ):ℝ) by linarith)
    have u : ∑ i,x i < (327:ℤ) := by exact_mod_cast (show ((∑ i,x i : ℤ):ℝ) < 327 by linarith)
    omega
  have sy : ∑ i, y i = 367 := by
    have l : (366:ℤ) < ∑ i,y i := by exact_mod_cast (show (366:ℝ) < ((∑ i,y i : ℤ):ℝ) by linarith)
    have u : ∑ i,y i < (368:ℤ) := by exact_mod_cast (show ((∑ i,y i : ℤ):ℝ) < 368 by linarith)
    omega
  let z := fun i => pilotColumn y i-pilotColumn x i
  have m : mean z = 41/40 := by dsimp [z]; rw [mean_sub,avg,avg,sx,sy]; norm_num
  let q := ∑ i, (y i-x i)^2
  have raw : ∑ i, z i^2 = (q:ℝ) := by simp [z,pilotColumn,q]
  have S : ss z = (q:ℝ)-40*(41/40)^2 := by
    have h := group_loss (by decide : 0 < 40) z z 0 0
    simp only [zero_mul,add_zero,sub_zero,zero_pow (by decide : 2 ≠ 0),zero_add,m,raw] at h
    norm_num at h ⊢
    linarith only [h]
  have tl := (abs_le.mp ht).1
  have tu := (abs_le.mp ht).2
  change -(1/200) ≤ pilotT z - 4.29 at tl
  change pilotT z - 4.29 ≤ 1/200 at tu
  have vz : 0 ≤ ss z/39 := div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
  have sp : sqrt (ss z/39) ≠ 0 := by
    intro h
    have h₀ : pilotT z = 0 := by simp [pilotT,h]
    linarith only [tl,h₀]
  have mt := div_mul_cancel₀ (mean z*sqrt 40) sp
  change pilotT z * sqrt (ss z/39) = _ at mt
  have sq := congrArg (fun v : ℝ => v^2) mt
  simp only [mul_pow,sq_sqrt vz,sq_sqrt (by norm_num : (0:ℝ) ≤ 40),m] at sq
  have vl := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4.285)
    (by linarith only [tl] : 4.285 ≤ pilotT z) 2) vz
  have vu := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith only [tl] : 0 ≤ pilotT z)
    (by linarith only [tu] : pilotT z ≤ 4.295) 2) vz
  rw [sq,S] at vl vu
  have l : (130:ℤ) < q := by exact_mod_cast (show (130:ℝ) < (q:ℝ) by linarith only [vu])
  have u : q < (132:ℤ) := by exact_mod_cast (show (q:ℝ) < 132 by linarith only [vl])
  have qe : q = 131 := by omega
  exact ⟨sx,sy,qe,m,by rw [S,qe]; norm_num⟩

/-- The usual two-way, single-measure absolute-agreement ICC(2,1), with
40 subjects, two occasions, and one degree of freedom for occasion. -/
noncomputable def pilotICC (u v c shift : ℝ) : ℝ :=
  let subject := (u+v+2*c)/(2*39)
  let error := (u+v-2*c)/(2*39)
  let occasion := 40*shift^2/2
  (subject-error)/(subject+error+2*(occasion-error)/40)

/-- A positive Pearson coefficient exceeds absolute agreement when the
between-occasion mean square exceeds the residual mean square. The pilot
moments recover exactly the systematic-shift condition used in §4.3. -/
theorem pilot_agreement_below_correlation (x y : PilotScores)
    (hx : RoundsTo (mean (pilotColumn x)) 8.15) (hy : RoundsTo (mean (pilotColumn y)) 9.18)
    (ht : RoundsTo (pilotT (fun i => pilotColumn y i-pilotColumn x i)) 4.29)
    (hr : |cross (pilotColumn x) (pilotColumn y) / sqrt (ss (pilotColumn x)*ss (pilotColumn y))-0.855| ≤ 1/2000) :
    let u := ss (pilotColumn x)
    let v := ss (pilotColumn y)
    let c := cross (pilotColumn x) (pilotColumn y)
    let shift := mean (pilotColumn y)-mean (pilotColumn x)
    pilotICC u v c shift < c/sqrt (u*v) := by
  intro u v c shift
  obtain ⟨_,_,_,m,S⟩ := pilot_integer_shift x y hx hy ht
  rw [mean_sub] at m
  have e : u+v-2*c = 3559/40 := by
    have co := cross_eq_of_gain (pilotColumn x) (pilotColumn y)
    rw [S] at co
    change c = (u+v-3559/40)/2 at co
    linarith only [co]
  have pos : 0 < c/sqrt (u*v) := by have := (abs_le.mp hr).1; change -(1/2000) ≤ c/sqrt (u*v)-0.855 at this; linarith
  have cp : 0 < c := (div_pos_iff.mp pos).elim And.left (fun h => False.elim (not_lt_of_ge (sqrt_nonneg _) h.2))
  have sp : 0 < sqrt (u*v) := (div_pos_iff.mp pos).elim And.right (fun h => False.elim (not_lt_of_ge (sqrt_nonneg _) h.2))
  have up : 0 ≤ u := sum_nonneg fun _ _ => sq_nonneg _
  have vp : 0 ≤ v := sum_nonneg fun _ _ => sq_nonneg _
  have am : 2*sqrt (u*v) ≤ u+v := by
    rw [sqrt_mul up]; nlinarith only [sq_nonneg (sqrt u-sqrt v),sq_sqrt up,sq_sqrt vp]
  change pilotICC u v c (mean (pilotColumn y)-mean (pilotColumn x)) < _
  rw [m,pilotICC]
  have den : 2*sqrt (u*v)/39 < (u+v+2*c)/(2*39)+(u+v-2*c)/(2*39)+
      2*(40*(41/40)^2/2-(u+v-2*c)/(2*39))/40 := by linarith only [am,e]
  have dp := lt_trans (by positivity : 0 < 2*sqrt (u*v)/39) den
  apply (div_lt_div_iff₀ dp sp).2
  have strict := mul_lt_mul_of_pos_left den cp
  linarith only [strict]

/-- Both reported p < 0.001 results for the pilot, using the Student
reference for the correlation test (38 df) and the paired test (39 df). -/
theorem pilot_significance {r t : ℝ} (hr : |r-0.855| ≤ 1/2000) (ht : RoundsTo t 4.29) :
    studentTwoSidedP 38 (sqrt 38 * (r/sqrt (1-r^2))) < 0.001 ∧ studentTwoSidedP 39 t < 0.001 := by
  have ref := (even_reference_scaled 18 (d:=sqrt 38) (by positivity) (by norm_num)
    0.68 0.56231002 0.56231003 0.00015 0.00017 (by decide +kernel)).2
  have lim : studentTwoSidedP 38 (sqrt 38*0.68) ≤ 0.00017 := by
    convert ref using 1
    norm_num
  obtain ⟨rl,ru⟩ := abs_le.mp hr
  have rp : 0 < r := by linarith
  have r2 := pow_le_pow_left₀ rp.le (show r ≤ 0.856 by linarith) 2
  have den := sqrt_pos.2 (show 0 < 1-r^2 by linarith only [r2])
  have den1 := sqrt_le_iff.2 ⟨zero_le_one,(by nlinarith only [sq_nonneg r] : 1-r^2 ≤ (1:ℝ)^2)⟩
  have ratio : 0.68 ≤ r/sqrt (1-r^2) := (le_div_iff₀ den).2 (by linarith only [den1,rl])
  have d := student_scaled_probability_antitone (by norm_num : (1:ℝ) ≤ 38) (by norm_num : (38:ℝ) ≤ 39)
    (by norm_num : (0:ℝ) < 0.68)
  have tlo := (abs_le.mp ht).1
  have upper := sqrt_le_iff.2 ⟨(by norm_num : (0:ℝ) ≤ 6.25),(by norm_num : (39:ℝ) ≤ 6.25^2)⟩
  have c : sqrt 39*0.68 ≤ t := by linarith only [upper,tlo]
  have prob (v a b : ℝ) (hv : 1 ≤ v) (ha : 0 ≤ a) (hab : a ≤ b) :
      studentTwoSidedP v b ≤ studentTwoSidedP v a := (studentProbability_strictAnti hv).antitoneOn ha (ha.trans hab) hab
  exact ⟨(prob _ _ _ (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left ratio (sqrt_nonneg _))).trans_lt
    (lim.trans_lt (by norm_num)),(prob _ _ _ (by norm_num) (by positivity) c).trans_lt (d.trans_lt (lim.trans_lt (by norm_num)))⟩

end Thesis.StudyANCOVA

