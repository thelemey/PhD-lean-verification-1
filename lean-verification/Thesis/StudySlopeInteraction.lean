import Thesis.StudentEvenDegrees
import Thesis.ThinkingANCOVA

open Real Set

namespace Thesis.StudyANCOVA

/-- The group-by-baseline interaction in §4.3 compares the two fitted slopes.
The unrestricted regression fits two intercepts and two slopes to 84 scores. -/
noncomputable def slopeInteractionSquared (xA yA xB yB : Fin 42 → ℝ) : ℝ :=
  let u := ss xA
  let v := ss xB
  let a := cross xA yA
  let b := cross xB yB
  let variance := ((ss yA-a^2/u)+(ss yB-b^2/v))/80
  (a/u-b/v)^2/(variance*(1/u+1/v))

theorem thinking_slope_statistic (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles)
    (htA : RoundsTo (pairedT (realScores A.gain)) 9.92)
    (htB : RoundsTo (pairedT (realScores B.gain)) 9.97) :
    slopeInteractionSquared A.paired.pre A.paired.post B.paired.pre B.paired.post =
      2923860240060/11034114722407 := by
  obtain ⟨⟨sa,qa⟩,⟨ta,ra⟩,⟨ga,_⟩,⟨sb,qb⟩,⟨tb,rb⟩,⟨gb,_⟩⟩ := thinking_integer_moments A B hA hB
  obtain ⟨va,vb⟩ := thinking_gain_squares A B hA hB htA htB
  unfold slopeInteractionSquared
  rw [cross_eq_of_gain,cross_eq_of_gain,gain_cast,gain_cast]
  norm_num [IntegerPair.paired, ss_integer, momentSS, sa,qa,ta,ra,ga,va,sb,qb,tb,rb,gb,vb]

private theorem interaction_reference :
    RoundsTo (studentTwoSidedP 80 (sqrt (2923860240060/11034114722407))) 0.61 := by
  let s : ℝ := 2923860240060/11034114722407
  let x := sqrt s/sqrt 80
  let y := sin (arctan x)
  have hs : 0 ≤ s := by dsimp [s]; norm_num
  have hy : 0 ≤ y := by dsimp [y]; rw [sin_arctan]; positivity
  have hx : x^2 = s/80 := by dsimp [x]; rw [div_pow,sq_sqrt hs,sq_sqrt (by norm_num : 0 ≤ (80:ℝ))]
  have hy2 : y^2 = s/(80+s) := by
    dsimp only [y]
    rw [sin_arctan,div_pow,sq_sqrt (by positivity),hx]
    have h : 0 < 80+s := by linarith
    field_simp
  have yl : (0.05745:ℝ) ≤ y := by
    have h : (0.05745:ℝ)^2 ≤ y^2 := by rw [hy2]; norm_num [s]
    nlinarith only [h,hy]
  have yu : y ≤ 0.05746 := by
    have h : y^2 ≤ (0.05746:ℝ)^2 := by rw [hy2]; norm_num [s]
    nlinarith only [h]
  have hm : y ∈ Icc (-1:ℝ) 1 := ⟨by linarith,by linarith⟩
  have elo := evenReduction_mono 39 (by norm_num : (0.05745:ℝ) ∈ Icc (-1) 1) hm yl
  have ehi := evenReduction_mono 39 hm (by norm_num : (0.05746:ℝ) ∈ Icc (-1) 1) yu
  have lo : evenReduction (0.05746:ℚ) 39 ≤ (1-0.605)*evenReduction 1 39 := by decide +kernel
  have hi : (1-0.615)*evenReduction (1:ℚ) 39 ≤ evenReduction 0.05745 39 := by decide +kernel
  have den : 0 < evenReduction (1:ℝ) 39 := by
    have h : 0 < evenReduction (1:ℚ) 39 := by decide +kernel
    have hc := (Rat.cast_pos (K := ℝ)).2 h
    simpa only [ratCast_evenReduction,Rat.cast_one] using hc
  have low := (Rat.cast_le (K := ℝ)).2 lo
  have high := (Rat.cast_le (K := ℝ)).2 hi
  simp only [Rat.cast_mul,Rat.cast_sub,Rat.cast_one,ratCast_evenReduction,Rat.cast_ofScientific] at low high
  have hp := studentTwoSidedP_even 39 (d := sqrt 80) (by positivity) (by norm_num) (sqrt s)
  simp only [Nat.cast_ofNat,show (2*39+2:ℝ)=80 by norm_num,abs_of_nonneg (sqrt_nonneg _)] at hp
  change studentTwoSidedP 80 (sqrt s) = 1-evenReduction y 39/evenReduction 1 39 at hp
  change RoundsTo (studentTwoSidedP 80 (sqrt s)) 0.61
  rw [hp]
  have hl := (div_le_iff₀ den).2 (ehi.trans low)
  have hu := (le_div_iff₀ den).2 (high.trans elo)
  exact abs_le.2 ⟨by linarith only [hl], by linarith only [hu]⟩

/-- The published p = 0.61 for testing a common baseline slope in the
thinking instrument follows from the descriptive table and paired t statistics. -/
theorem thinking_slope_interaction_probability (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles)
    (htA : RoundsTo (pairedT (realScores A.gain)) 9.92)
    (htB : RoundsTo (pairedT (realScores B.gain)) 9.97) :
    RoundsTo (studentTwoSidedP 80 (sqrt
      (slopeInteractionSquared A.paired.pre A.paired.post B.paired.pre B.paired.post))) 0.61 := by
  rw [thinking_slope_statistic A B hA hB htA htB]
  exact interaction_reference


private theorem ss_of_rounded_sd {x : Fin 42 → ℝ} {s : ℝ} (hs : 1/200 ≤ s)
    (h : RoundsTo (sampleSD x) s) :
    41*(s-1/200)^2 ≤ ss x ∧ ss x ≤ 41*(s+1/200)^2 := by
  obtain ⟨lo,hi⟩ := abs_le.mp h
  have l := pow_le_pow_left₀ (sub_nonneg.2 hs) (by linarith : s-1/200 ≤ sampleSD x) 2
  have u := pow_le_pow_left₀ (show 0 ≤ sampleSD x from sqrt_nonneg _) (by linarith : sampleSD x ≤ s+1/200) 2
  rw [sampleSD_sq] at l u
  exact ⟨by linarith,by linarith⟩

private theorem slope_range (g : PairedGroup) {a b c l u : ℝ}
    (ha : RoundsTo g.summary.preSD a) (hb : RoundsTo g.summary.postSD b) (hc : RoundsTo g.summary.gainSD c)
    (a₀ : 1/200 < a) (b₀ : 1/200 ≤ b) (c₀ : 1/200 ≤ c) (l₀ : 0 ≤ l) (u₀ : 0 ≤ u)
    (low : l*(41*(a+1/200)^2) ≤ (41*(a-1/200)^2+41*(b-1/200)^2-41*(c+1/200)^2)/2)
    (high : (41*(a+1/200)^2+41*(b+1/200)^2-41*(c-1/200)^2)/2 ≤ u*(41*(a-1/200)^2))
    (cap : 41*(a+1/200)^2 ≤ 26000)
    (rss : 10000 ≤ 41*(b-1/200)^2-u^2*(41*(a+1/200)^2)) :
    let x := ss g.pre
    let y := ss g.post
    let xy := cross g.pre g.post
    0 < x ∧ x ≤ 26000 ∧ l ≤ xy/x ∧ xy/x ≤ u ∧ 10000 ≤ y-xy^2/x := by
  obtain ⟨xl,xu⟩ := ss_of_rounded_sd a₀.le ha
  obtain ⟨yl,yu⟩ := ss_of_rounded_sd b₀ hb
  obtain ⟨gl,gu⟩ := ss_of_rounded_sd c₀ hc
  have xp : 0 < ss g.pre := (show 0 < 41*(a-1/200)^2 by have := sub_pos.2 a₀; positivity).trans_le xl
  have he := cross_eq_of_gain g.pre g.post
  have lo : l ≤ cross g.pre g.post / ss g.pre := (le_div_iff₀ xp).2 (by
    linarith only [mul_le_mul_of_nonneg_left xu l₀,low,he,xl,yl,gu])
  have hi : cross g.pre g.post / ss g.pre ≤ u := (div_le_iff₀ xp).2 (by
    linarith only [mul_le_mul_of_nonneg_left xl u₀,high,he,xu,yu,gl])
  have sqh := mul_le_mul (pow_le_pow_left₀ (l₀.trans lo) hi 2) xu xp.le (sq_nonneg u)
  have id : (cross g.pre g.post / ss g.pre)^2 * ss g.pre = (cross g.pre g.post)^2 / ss g.pre := by
    field_simp
    ring
  rw [id] at sqh
  exact ⟨xp,xu.trans cap,lo,hi,by linarith only [yl,sqh,rss]⟩

/-- For the hundred-point instrument the interaction is nonsignificant
throughout the rounding intervals for the six printed standard deviations. -/
theorem numbers_slope_interaction (A B : PairedGroup)
    (hA : MatchesTable A.summary numbersControl) (hB : MatchesTable B.summary numbersPuzzles) :
    let t₂ := slopeInteractionSquared A.pre A.post B.pre B.post
    t₂ < 0.01 ∧ 0.05 < studentTwoSidedP 80 (sqrt t₂) := by
  obtain ⟨xa,ca,la,ua,ra⟩ := slope_range A (a := 24.68) (b := 21.61) (c := 21.08) (l := 0.517) (u := 0.520)
    hA.preSD hA.postSD hA.gainSD (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨xb,cb,lb,ub,rb⟩ := slope_range B (a := 22.11) (b := 20.19) (c := 19.50) (l := 0.527) (u := 0.530)
    hB.preSD hB.postSD hB.gainSD (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let d := cross A.pre A.post/ss A.pre - cross B.pre B.post/ss B.pre
  let v := ((ss A.post-(cross A.pre A.post)^2/ss A.pre)+(ss B.post-(cross B.pre B.post)^2/ss B.pre))/80
  have dv : 250 ≤ v := by dsimp [v]; linarith only [ra,rb]
  have dd : d^2 ≤ 0.013^2 := by
    rw [← sq_abs d]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.2 ⟨by dsimp [d]; linarith only [la,ub],
      by dsimp [d]; linarith only [ua,lb]⟩) 2
  have fac : 2/26000 ≤ 1/ss A.pre+1/ss B.pre := by
    linarith only [one_div_le_one_div_of_le xa ca,one_div_le_one_div_of_le xb cb]
  have var := mul_le_mul dv fac (by norm_num) (by linarith only [dv] : 0 ≤ v)
  have hp : 0 < v*(1/ss A.pre+1/ss B.pre) := (by norm_num : (0:ℝ) < 250*(2/26000)).trans_le var
  have ht : d^2/(v*(1/ss A.pre+1/ss B.pre)) < 0.01 := (div_lt_iff₀ hp).2 (by linarith only [dd,var])
  refine ⟨ht, (study_student_p_cutoffs (by norm_num : (80:ℝ) ≤ 80) (by norm_num)).1 _ ?_⟩
  rw [abs_of_nonneg (sqrt_nonneg _)]
  exact sqrt_le_iff.2 ⟨by norm_num,ht.le.trans (by norm_num)⟩


/-- Difference between the common-slope residual sum of squares and the
two-slope residual sum of squares. Dividing by the unrestricted residual
variance gives the F statistic for the one additional coefficient. -/
theorem slopeInteraction_eq_nested (A B : PairedGroup) (ha : 0 < ss A.pre) (hb : 0 < ss B.pre) :
    let x := ss A.pre
    let y := ss B.pre
    let u := cross A.pre A.post
    let v := cross B.pre B.post
    let common := ss A.post+ss B.post-(u+v)^2/(x+y)
    let separate := (ss A.post-u^2/x)+(ss B.post-v^2/y)
    slopeInteractionSquared A.pre A.post B.pre B.post = (common-separate)/(separate/80) := by
  intro x y u v common separate
  have hx : 0 < x := ha
  have hy : 0 < y := hb
  have hxy : 0 < x+y := add_pos hx hy
  have hfac : 0 < 1/x+1/y := by positivity
  have diff : ((u/x-v/y)^2)/(1/x+1/y) = common-separate := by
    dsimp only [common,separate]
    field_simp [hx.ne',hy.ne',hxy.ne',hfac.ne']
    ring
  change (u/x-v/y)^2/((separate/80)*(1/x+1/y)) = _
  rw [← diff,div_div,mul_comm (separate/80)]

/-- Single-group least-squares error with its own intercept and slope. -/
theorem separate_regression_residual (x y : Fin 42 → ℝ) (hx : 0 < ss x) (slope intercept : ℝ) :
    (∑ i, (y i-(intercept+slope*x i))^2) =
      ss y-(cross x y)^2/ss x + (slope-cross x y/ss x)^2*ss x +
        42*(mean y-intercept-slope*mean x)^2 := by
  rw [group_loss (by norm_num : 0 < 42)]
  push_cast
  field_simp [hx.ne']
  ring

/-- Pearson's within-group correlations for the twelve-point instrument. -/
theorem thinking_baseline_correlations (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles)
    (htA : RoundsTo (pairedT (realScores A.gain)) 9.92)
    (htB : RoundsTo (pairedT (realScores B.gain)) 9.97) :
    let r := fun (g : PairedGroup) => cross g.pre g.post / sqrt (ss g.pre * ss g.post)
    RoundsTo (r A.paired) 0.03 ∧ RoundsTo (r B.paired) (-0.09) := by
  obtain ⟨⟨sa,qa⟩,⟨ta,ra⟩,⟨ga,_⟩,⟨sb,qb⟩,⟨tb,rb⟩,⟨gb,_⟩⟩ := thinking_integer_moments A B hA hB
  obtain ⟨va,vb⟩ := thinking_gain_squares A B hA hB htA htB
  dsimp only
  rw [cross_eq_of_gain,cross_eq_of_gain,gain_cast,gain_cast]
  simp only [IntegerPair.paired,ss_integer,momentSS,sa,qa,ta,ra,ga,va,sb,qb,tb,rb,gb,vb,Int.cast_ofNat]
  constructor
  · let z := sqrt ((526-(114:ℝ)^2/42)*(3205-347^2/42))
    have zl : 270 ≤ z := le_sqrt_of_sq_le (by norm_num)
    have zu : z ≤ 271 := sqrt_le_iff.2 ⟨by norm_num,by norm_num⟩
    change RoundsTo (_/z) _
    rw [RoundsTo,abs_le]
    constructor
    · apply le_sub_iff_add_le.2
      apply (le_div_iff₀ (by linarith : 0 < z)).2
      linarith only [zu]
    · apply sub_le_iff_le_add.2
      apply (div_le_iff₀ (by linarith : 0 < z)).2
      linarith only [zl]
  · let z := sqrt ((790-(158:ℝ)^2/42)*(3891-389^2/42))
    have zl : 237 ≤ z := le_sqrt_of_sq_le (by norm_num)
    have zu : z ≤ 238 := sqrt_le_iff.2 ⟨by norm_num,by norm_num⟩
    change RoundsTo (_/z) _
    rw [RoundsTo,abs_le]
    constructor
    · apply le_sub_iff_add_le.2
      apply (le_div_iff₀ (by linarith : 0 < z)).2
      linarith only [zl]
    · apply sub_le_iff_le_add.2
      apply (div_le_iff₀ (by linarith : 0 < z)).2
      linarith only [zu]


/-- A quantitative lower bound for the hundred-point slope test from the
rounded descriptive table, without using the printed interaction p value. -/
theorem numbers_slope_probability_bound (A B : PairedGroup)
    (hA : MatchesTable A.summary numbersControl) (hB : MatchesTable B.summary numbersPuzzles) :
    0.92 ≤ studentTwoSidedP 80 (sqrt (slopeInteractionSquared A.pre A.post B.pre B.post)) := by
  let s := slopeInteractionSquared A.pre A.post B.pre B.post
  have h := (numbers_slope_interaction A B hA hB).1
  have ht : sqrt s ≤ 0.1 := sqrt_le_iff.2 ⟨by norm_num,h.le.trans (by norm_num)⟩
  let x := sqrt s / sqrt 80
  let y := sin (arctan x)
  have xp : 0 ≤ x := by dsimp [x]; positivity
  have dx := le_sqrt_of_sq_le (by norm_num : (8.94:ℝ)^2 ≤ 80)
  have xu : x ≤ 0.01119 := (div_le_iff₀ (by positivity)).2 (by linarith only [ht,dx])
  have yp : 0 ≤ y := by dsimp [y]; rw [sin_arctan]; positivity
  have yu : y ≤ 0.01119 := by
    have hd : 1 ≤ sqrt (1+x^2) := le_sqrt_of_sq_le (by nlinarith only [sq_nonneg x])
    dsimp [y]
    rw [sin_arctan]
    exact (div_le_iff₀ (by positivity)).2 (by linarith only [xu,hd])
  have m := evenReduction_mono 39 (show y ∈ Icc (-1:ℝ) 1 from ⟨by linarith,by linarith⟩)
    (by norm_num : (0.01119:ℝ) ∈ Icc (-1) 1) yu
  have ref : evenReduction (0.01119:ℚ) 39 ≤ (1-0.92)*evenReduction 1 39 := by decide +kernel
  have rr := (Rat.cast_le (K := ℝ)).2 ref
  simp only [Rat.cast_mul,Rat.cast_sub,Rat.cast_one,ratCast_evenReduction,Rat.cast_ofScientific] at rr
  have hdq : 0 < evenReduction (1:ℚ) 39 := by decide +kernel
  have den := (Rat.cast_pos (K := ℝ)).2 hdq
  simp only [ratCast_evenReduction,Rat.cast_one] at den
  have hp := studentTwoSidedP_even 39 (d := sqrt 80) (by positivity) (by norm_num) (sqrt s)
  simp only [Nat.cast_ofNat,show (2*39+2:ℝ)=80 by norm_num,abs_of_nonneg (sqrt_nonneg _)] at hp
  change studentTwoSidedP 80 (sqrt s) = 1-evenReduction y 39/evenReduction 1 39 at hp
  change 0.92 ≤ studentTwoSidedP 80 (sqrt s)
  rw [hp]
  linarith only [(div_le_iff₀ den).2 (m.trans rr)]

end Thesis.StudyANCOVA
