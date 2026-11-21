import Thesis.StudyIntegerMoments

namespace Thesis.StudyANCOVA

/-- Paired t statistic for the mean change among the 42 pupils. -/
noncomputable def pairedT (gain : Fin 42 → ℝ) : ℝ :=
  mean gain * Real.sqrt 42 / sampleSD gain

theorem pairedT_sq_of_moments (x : IntegerScores) :
    pairedT (realScores x)^2 =
      ((total x : ℝ)/42)^2 * 42 / (momentSS (total x) (squareTotal x) / 41) := by
  rw [pairedT, div_pow, mul_pow, mean_integer, Real.sq_sqrt (by norm_num), sampleSD_sq, ss_integer]

private theorem sq_of_rounding {t r : ℝ} (hr : 1/200 ≤ r) (h : RoundsTo t r) :
    (r-1/200)^2 ≤ t^2 ∧ t^2 ≤ (r+1/200)^2 := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  exact ⟨pow_le_pow_left₀ (by linarith) (by linarith) 2,
    pow_le_pow_left₀ (by linarith) (by linarith) 2⟩

/-- The separately printed paired tests (9.92 and 9.97) resolve the two
rounding ambiguities for the gain sums of squares. Combined with the
descriptive table they determine the sufficient statistics for ANCOVA. -/
theorem thinking_pooled_moments (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles)
    (htA : RoundsTo (pairedT (realScores A.gain)) 9.92)
    (htB : RoundsTo (pairedT (realScores B.gain)) 9.97) :
    let a := A.paired.summary
    let b := B.paired.summary
    a.pre = 114/42 ∧ b.pre = 158/42 ∧ a.post = 347/42 ∧ b.post = 389/42 ∧
    withinSS a.preSD b.preSD = 8656/21 ∧ withinSS a.postSD b.postSD = 13151/21 ∧
    withinSS a.gainSD b.gainSD = 22321/21 := by
  obtain ⟨⟨sa,qa⟩,⟨ta,ra⟩,⟨ga,va⟩,⟨sb,qb⟩,⟨tb,rb⟩,⟨gb,vb⟩⟩ := thinking_integer_moments A B hA hB
  have ta' := (sq_of_rounding (by norm_num) htA).2
  have tb' := (sq_of_rounding (by norm_num) htB).1
  rw [pairedT_sq_of_moments, ga] at ta'
  rw [pairedT_sq_of_moments, gb] at tb'
  have va' : squareTotal A.gain = 1831 := by
    rcases va with h | h
    · norm_num [h, momentSS] at ta'
    · exact h
  have vb' : squareTotal B.gain = 1795 := by
    rcases vb with h | h
    · exact h
    · norm_num [h, momentSS] at tb'
  dsimp only [PairedGroup.summary]
  rw [gain_cast, gain_cast]
  change mean (realScores A.pre) = _ ∧ mean (realScores B.pre) = _ ∧
    mean (realScores A.post) = _ ∧ mean (realScores B.post) = _ ∧
    withinSS (sampleSD (realScores A.pre)) (sampleSD (realScores B.pre)) = _ ∧
    withinSS (sampleSD (realScores A.post)) (sampleSD (realScores B.post)) = _ ∧ _
  norm_num [mean_integer, withinSS_sampleSD, ss_integer, momentSS, sa, sb, ta, tb, ga, gb, qa, qb,
    ra, rb, va', vb']

noncomputable def ancovaContrast (A B : GroupSummary) : ℝ :=
  let xx := withinSS A.preSD B.preSD
  let xy := (xx + withinSS A.postSD B.postSD - withinSS A.gainSD B.gainSD)/2
  adjustedDifference (B.pre-A.pre) (B.post-A.post) xx xy

noncomputable def ancovaStandardErrorSq (A B : GroupSummary) : ℝ :=
  let xx := withinSS A.preSD B.preSD
  let yy := withinSS A.postSD B.postSD
  let xy := (xx+yy-withinSS A.gainSD B.gainSD)/2
  residualVariance xx yy xy * (1/21+(B.pre-A.pre)^2/xx)

/-- Exact reconstruction of the adjusted contrast, its squared standard
error and the test statistic from independent published summaries. -/
theorem thinking_exact_ancova (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles)
    (htA : RoundsTo (pairedT (realScores A.gain)) 9.92)
    (htB : RoundsTo (pairedT (realScores B.gain)) 9.97) :
    let a := A.paired.summary
    let b := B.paired.summary
    ancovaContrast a b = 93715/90888 ∧
    ancovaStandardErrorSq a b = 259962180995/669110912064 ∧
    ancovaSquaredT a b = 142276519845/51992436199 := by
  obtain ⟨a,b,c,d,x,y,g⟩ := thinking_pooled_moments A B hA hB htA htB
  dsimp only
  norm_num [ancovaContrast, ancovaStandardErrorSq, ancovaSquaredT, squaredT, adjustedDifference,
    residualVariance, a,b,c,d,x,y,g]

/-- The adjusted means evaluated at the pooled baseline, the contrast, t and
partial eta squared give the published entries at their displayed precisions. -/
theorem thinking_adjusted_table_roundings (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles)
    (htA : RoundsTo (pairedT (realScores A.gain)) 9.92)
    (htB : RoundsTo (pairedT (realScores B.gain)) 9.97) :
    let a := A.paired.summary
    let b := B.paired.summary
    let g := ancovaContrast a b
    let t₂ := ancovaSquaredT a b
    RoundsTo ((a.post+b.post-g)/2) 8.25 ∧ RoundsTo ((a.post+b.post+g)/2) 9.28 ∧
    RoundsTo g 1.03 ∧ RoundsTo (Real.sqrt t₂) 1.65 ∧
    |t₂/(t₂+81) - 0.033| ≤ 1/2000 := by
  obtain ⟨_,_,ma,mb,_⟩ := thinking_pooled_moments A B hA hB htA htB
  obtain ⟨hg,_,ht⟩ := thinking_exact_ancova A B hA hB htA htB
  dsimp only
  rw [ma,mb,hg,ht]
  have lo := Real.le_sqrt_of_sq_le (by norm_num : (1.6542:ℝ)^2 ≤ 142276519845/51992436199)
  have hi := Real.sqrt_le_iff.2 ⟨by norm_num, (by norm_num : (142276519845:ℝ)/51992436199 ≤ 1.6543^2)⟩
  refine ⟨by norm_num [RoundsTo, abs_le], by norm_num [RoundsTo, abs_le], by norm_num [RoundsTo, abs_le], ?_, by rw [abs_le]; constructor <;> norm_num⟩
  exact abs_le.2 ⟨by linarith only [lo], by linarith only [hi]⟩

end Thesis.StudyANCOVA
