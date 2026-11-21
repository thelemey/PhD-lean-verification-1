import Thesis.NumbersANCOVA

open Real Set

namespace Thesis.StudyANCOVA

/-- Section 4.3 assigns one whole class to each method. With the control
class as reference, the two indicators have the same value for every pupil.
A free classroom offset and a method coefficient therefore enter the fitted
model only as their sum, even after adjustment for the pre-test. -/
theorem class_and_method_same_fit {n : ℕ} (hn : 0 < n) (xA yA xB yB : Fin n → ℝ)
    (hx : 0 < ss xA + ss xB) :
    let b := (cross xA yA + cross xB yB)/(ss xA + ss xB)
    let a := mean yA - b*mean xA
    let g := mean yB - mean yA - b*(mean xB - mean xA)
    ∀ method : ℝ, ∃ classroom : ℝ,
      (∀ i, a + method + classroom + b*xB i = a + g + b*xB i) ∧
      ∀ u v w slope, loss xA yA xB yB a (method+classroom) b ≤ loss xA yA xB yB u (v+w) slope := by
  intro b a g method
  refine ⟨g-method,fun i => by ring,?_⟩
  intro u v w slope
  rw [show method+(g-method)=g by ring]
  exact loss_minimizer hn xA yA xB yB hx u (v+w) slope

/-- Direct checks of the sensitivity paragraph for the twelve-question test.
Both published detection thresholds exceed the adjusted point estimate.
The 95% interval includes zero and a benefit of half a residual SD. -/
theorem thinking_sensitivity_interpretation (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl) (hB : MatchesTable B.paired.summary thinkingPuzzles)
    (htA : RoundsTo (pairedT (realScores A.gain)) 9.92)
    (htB : RoundsTo (pairedT (realScores B.gain)) 9.97) :
    let a := A.paired.summary
    let b := B.paired.summary
    let g := ancovaContrast a b
    let sd := sqrt (ancovaResidualVariance a b)
    let se := sqrt (ancovaStandardErrorSq a b)
    let ci := Icc (g-critical95*se) (g+critical95*se)
    RoundsTo sd 2.78 ∧ RoundsTo (g/sd) 0.37 ∧
    0 < g ∧ g < 1.72 ∧ g < 1.99 ∧ (0:ℝ) ∈ ci ∧ sd/2 ∈ ci := by
  intro a b g sd se ci
  obtain ⟨_,_,_,_,xx,yy,gg⟩ := thinking_pooled_moments A B hA hB htA htB
  obtain ⟨hg,_,_⟩ := thinking_exact_ancova A B hA hB htA htB
  obtain ⟨_,hL,hU⟩ := thinking_ancova_probability_and_interval A B hA hB htA htB
  have hv : ancovaResidualVariance a b = 113769007/14723856 := by
    norm_num [ancovaResidualVariance,residualVariance,xx,yy,gg,a,b]
  have s : Bounds sd 2.7797 2.7798 := by
    dsimp only [sd]
    rw [hv]
    exact ⟨le_sqrt_of_sq_le (by norm_num),sqrt_le_iff.2 ⟨by norm_num,by norm_num⟩⟩
  have g' : Bounds g 1.0310 1.0312 := by
    dsimp only [g,a,b]
    rw [hg]
    constructor <;> norm_num
  have d := (g'.div s (by decide +kernel) (by decide +kernel)).rounds 0.37 (by decide +kernel) (by decide +kernel)
  obtain ⟨_,lo⟩ := abs_le.mp hL
  obtain ⟨hi,_⟩ := abs_le.mp hU
  change g-critical95*se-(-0.21) ≤ 1/200 at lo
  change -(1/200) ≤ g+critical95*se-2.27 at hi
  have sl := s.lower
  have su := s.upper
  simp only [Rat.cast_ofScientific] at sl su
  refine ⟨s.rounds 2.78 (by decide +kernel) (by decide +kernel), d,?_,?_,?_,?_,?_⟩
  · change 0 < ancovaContrast A.paired.summary B.paired.summary
    rw [hg]; norm_num
  · change ancovaContrast A.paired.summary B.paired.summary < 1.72
    rw [hg]; norm_num
  · change ancovaContrast A.paired.summary B.paired.summary < 1.99
    rw [hg]; norm_num
  · exact ⟨by linarith only [lo],by linarith only [hi]⟩
  · exact ⟨by linarith only [lo,sl],by linarith only [hi,su]⟩

/-- The same interpretation on the hundred-point scale, using the actual
rounding uncertainty of the descriptive table. The thresholds 10.55 and
12.21 are the two design values supplied by the dissertation. -/
theorem numbers_sensitivity_interpretation (A B : PairedGroup)
    (hA : MatchesTable A.summary numbersControl) (hB : MatchesTable B.summary numbersPuzzles) :
    let a := A.summary
    let b := B.summary
    let g := ancovaContrast a b
    let sd := sqrt (ancovaResidualVariance a b)
    let se := sqrt (ancovaStandardErrorSq a b)
    let ci := Icc (g-critical95*se) (g+critical95*se)
    Bounds sd 17.045 17.062 ∧ 0 < g ∧ g < 10.55 ∧ g < 12.21 ∧ (0:ℝ) ∈ ci ∧ sd/2 ∈ ci := by
  intro a b g sd se ci
  obtain ⟨_,v,ctr,_⟩ := numbers_adjustment_from_summaries a b hA hB A.summary_gain B.summary_gain
  obtain ⟨_,_,lo,hi,_,_⟩ := numbers_ancova_from_paired_scores A B hA hB
  have s := v.sqrt 17.045 17.062 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have gl := ctr.lower
  have gu := ctr.upper
  have L : g-critical95*se ≤ (-1.400:ℚ) := lo.upper
  have U : (13.856:ℚ) ≤ g+critical95*se := hi.lower
  have sl : (17.045:ℚ) ≤ sd := s.lower
  have su : sd ≤ (17.062:ℚ) := s.upper
  change (6.2158:ℚ) ≤ g at gl
  change g ≤ (6.2401:ℚ) at gu
  simp only [Rat.cast_ofScientific,Rat.cast_neg] at L U sl su gl gu
  exact ⟨s,by linarith only [gl],by linarith only [gu],by linarith only [gu],
    ⟨by linarith only [L],by linarith only [U]⟩,⟨by linarith only [L,sl],by linarith only [U,su]⟩⟩

end Thesis.StudyANCOVA
