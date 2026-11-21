import Thesis.NumbersWelch

open Real Set

namespace Thesis.StudyANCOVA

private theorem gain_contrast (A B : IntegerPair) (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles) :
    B.paired.summary.gain - A.paired.summary.gain = -2/42 := by
  obtain ⟨_,_,⟨sa,_⟩,_,_,⟨sb,_⟩⟩ := thinking_integer_moments A B hA hB
  simp only [PairedGroup.summary,gain_cast,mean_integer,sa,sb]
  norm_num

/-- Between-class difference of thinking-test gains. Integer totals determine
the signed contrast exactly. The descriptive table alone fixes the displayed
Welch statistic, degrees of freedom and two-sided probability. -/
theorem thinking_welch_gain (A B : IntegerPair) (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles) :
    let a := A.paired.summary
    let b := B.paired.summary
    let d := b.gain-a.gain
    d = -2/42 ∧ RoundsTo (d/welchSE a.gainSD b.gainSD) (-0.06) ∧
    |welchDF a.gainSD b.gainSD-82| ≤ 1/20 ∧ RoundsTo (welchP d a.gainSD b.gainSD) 0.95 := by
  intro a b d
  have de : d = -2/42 := gain_contrast A B hA hB
  obtain ⟨df,se⟩ := welch_df_se_bounds 3.62 3.58 hA.gainSD hB.gainSD
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 81.98 82 0.7844 0.7868
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have pos := ((Bounds.exactValue (2/42)).div se (by decide +kernel) (by decide +kernel)).widen
    (l:=0.06050) (u:=0.06072) (by decide +kernel) (by decide +kernel)
  have hpos : Bounds ((2/42)/welchSE a.gainSD b.gainSD) 0.06050 0.06072 := by simpa only [Rat.cast_div,Rat.cast_ofNat] using pos
  have hp := small_welch_box df hpos (x:=0.006681) (y:=0.006707)
    (l₁:=0.9524) (u₁:=0.9526) (l₂:=0.9517) (u₂:=0.9518)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0.00668085 0.00668086 0.00670684 0.00670685
    (by decide +kernel) (by decide +kernel)
  have pe : welchP (-2/42) a.gainSD b.gainSD = welchP (2/42) a.gainSD b.gainSD := by
    simp [welchP,welchSquared,div_pow]
  obtain ⟨lo,hi⟩ := df
  obtain ⟨tl,tu⟩ := hpos
  simp only [Rat.cast_ofScientific,Rat.cast_ofNat] at lo hi tl tu
  rw [de,pe,welchP_eq_of_positive (by norm_num : (0:ℝ) ≤ 2/42)]
  exact ⟨rfl,abs_le.2 ⟨by simp only [neg_div]; linarith only [tu],by simp only [neg_div]; linarith only [tl]⟩,
    abs_le.2 ⟨by linarith only [lo],by linarith only [hi]⟩,
    hp.rounds 0.95 (by decide +kernel) (by decide +kernel)⟩

/-- The two paired statistics printed in the text resolve the rounded gain
variances. They suffice for both endpoints of its 95% interval. -/
theorem thinking_welch_gain_interval (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles)
    (htA : RoundsTo (pairedT (realScores A.gain)) 9.92)
    (htB : RoundsTo (pairedT (realScores B.gain)) 9.97) :
    let a := A.paired.summary
    let b := B.paired.summary
    WelchInterval (b.gain-a.gain) (withinSS a.gainSD b.gainSD) (welchDF a.gainSD b.gainSD) (-1.61) 1.52 := by
  intro a b
  obtain ⟨_,_,_,_,_,_,S⟩ := thinking_pooled_moments A B hA hB htA htB
  obtain ⟨df,_⟩ := welch_df_se_bounds 3.62 3.58 hA.gainSD hB.gainSD
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 81.98 82 0.7844 0.7868
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  let v := welchDF a.gainSD b.gainSD
  have vl : 81 ≤ v := (by norm_num : (81:ℝ) ≤ (81.98:ℚ)).trans df.lower
  have vu : v ≤ 82 := by exact_mod_cast df.upper
  obtain ⟨c,hc,he,_⟩ := welch_critical95_bounds vl (by linarith)
  have ref := even_reference_scaled 40 (d:=sqrt 82) (by positivity) (by norm_num)
    0.219660 0.21454501 0.21454502 0.05002 0.05003 (by decide +kernel)
  have refl : (0.05002:ℝ) ≤ studentTwoSidedP 82 (sqrt 82*0.21966) := by
    convert ref.1 using 1
    norm_num
  have xle : (1.989:ℝ) ≤ sqrt 82 * 0.21966 := by
    have h := le_sqrt_of_sq_le (by norm_num : (9.05538:ℝ)^2 ≤ 82)
    linarith only [h]
  have atL := (studentProbability_strictAnti (v:=82) (by norm_num)).antitoneOn
    (by norm_num : (1.989:ℝ) ∈ Ici 0) (by change 0 ≤ sqrt 82*0.21966; positivity) xle
  have deg := student_probability_antitone_degrees (by linarith : 79 ≤ v) vu (by norm_num : (1.5:ℝ) ≤ 1.989)
  have ch : 1.989 ≤ c := by
    by_contra! z
    have H := studentProbability_strictAnti (by linarith : 1 ≤ v)
      (by change 0 ≤ c; linarith [hc.1]) (by norm_num : (1.989:ℝ) ∈ Ici 0) z
    linarith only [H,he,deg,refl,atL]
  rw [gain_contrast A B hA hB,S]
  have sl := le_sqrt_of_sq_le (by norm_num : (0.7856526:ℝ)^2 ≤ (22321/21)/(41*42))
  have su := sqrt_le_iff.2 ⟨(by norm_num : (0:ℝ) ≤ 0.7856528), (by norm_num : (22321/21)/(41*42) ≤ (0.7856528:ℝ)^2)⟩
  have c0 : 0 ≤ c := by linarith
  have w₁ := mul_le_mul ch sl (by norm_num : (0:ℝ) ≤ 0.7856526) c0
  have w₂ := mul_le_mul hc.2 su (sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1.991)
  exact ⟨c,c0,he,abs_le.2 ⟨by linarith only [w₂],by linarith only [w₁]⟩,
    abs_le.2 ⟨by linarith only [w₁],by linarith only [w₂]⟩⟩

end Thesis.StudyANCOVA

