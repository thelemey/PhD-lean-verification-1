import Thesis.NumbersANCOVA
import Thesis.StudySummaryPrecision
import Thesis.ThinkingRanks

open Real Set

namespace Thesis.StudyANCOVA

/-- Fit post-test on a class indicator and the pre-test, using both classes'
within-class sums. Group B is the class taught with puzzles. -/
noncomputable def fittedGroupContrast (a b : PairedGroup) : ℝ :=
  let slope := (cross a.pre a.post + cross b.pre b.post) / (ss a.pre + ss b.pre)
  mean b.post - mean a.post - slope * (mean b.pre - mean a.pre)

/-- The primary two-sided test of the fitted group coefficient in §4.3.
The denominator uses the residual sum of squares at the least-squares fit.
There are 84 pupils and three fitted parameters. -/
noncomputable def fittedGroupP (a b : PairedGroup) : ℝ :=
  let xx := ss a.pre + ss b.pre
  let slope := (cross a.pre a.post + cross b.pre b.post) / xx
  let intercept := mean a.post - slope * mean a.pre
  let g := fittedGroupContrast a b
  let mse := loss a.pre a.post b.pre b.post intercept g slope / 81
  studentTwoSidedP 81 (sqrt (g^2 / (mse * (2/42 + (mean b.pre - mean a.pre)^2 / xx))))

private theorem fitted_from_summary (a b : PairedGroup) (pos : 0 < a.summary.preSD) :
    fittedGroupContrast a b = ancovaContrast a.summary b.summary ∧
    fittedGroupP a b = ancovaP a.summary b.summary := by
  have variance := sqrt_pos.mp pos
  change 0 < ss a.pre / 41 at variance
  have other : 0 ≤ ss b.pre := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hx : 0 < ss a.pre + ss b.pre := by linarith
  constructor
  · unfold fittedGroupContrast ancovaContrast adjustedDifference PairedGroup.summary
    dsimp only
    rw [← pooled_cross_of_sampleSD, withinSS_sampleSD]
  · exact congrArg (fun t₂ => studentTwoSidedP 81 (sqrt t₂))
      (ancovaSquaredT_eq_fitted_statistic a b hx).symm

/-- For the integer instrument, using only the descriptive table leaves
two possible gain sums of squares per class. All four combinations give
the same reported adjusted contrast to two decimals and the same decision. -/
theorem thinking_primary_from_descriptive (a b : IntegerPair)
    (ha : MatchesTable a.paired.summary thinkingControl)
    (hb : MatchesTable b.paired.summary thinkingPuzzles) :
    RoundsTo (ancovaContrast a.paired.summary b.paired.summary) 1.03 ∧
    Bounds (ancovaP a.paired.summary b.paired.summary) 0.1010 0.1029 := by
  obtain ⟨⟨ax,axx⟩,⟨ay,ayy⟩,⟨ag,agg⟩,⟨bx,bxx⟩,⟨by',byy⟩,⟨bg,bgg⟩⟩ :=
    thinking_integer_moments a b ha hb
  have stats : RoundsTo (ancovaContrast a.paired.summary b.paired.summary) 1.03 ∧
      (1.6500:ℝ)^2 ≤ ancovaSquaredT a.paired.summary b.paired.summary ∧
      ancovaSquaredT a.paired.summary b.paired.summary ≤ (1.6584:ℝ)^2 := by
    unfold ancovaContrast ancovaSquaredT
    dsimp only [PairedGroup.summary]
    rw [gain_cast, gain_cast]
    rcases agg with h|h <;> rcases bgg with k|k <;>
      norm_num [IntegerPair.paired, withinSS_sampleSD, mean_integer, ss_integer, momentSS,
        adjustedDifference, squaredT, residualVariance, RoundsTo, abs_le,
        ax,axx,ay,ayy,ag,h,bx,bxx,by',byy,bg,k]
  obtain ⟨contrast,sl,su⟩ := stats
  have lo := (reference81 1.6584 0.1010 0.1012 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  have hi := (reference81 1.6500 0.1027 0.1029 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2
  have mono := (studentProbability_strictAnti (v:=81) (by norm_num)).antitoneOn
  simp only [Rat.cast_ofScientific] at lo hi
  exact ⟨contrast,lo.trans (mono (sqrt_nonneg _) (by norm_num : (1.6584:ℝ) ∈ Ici 0)
    (sqrt_le_iff.2 ⟨by norm_num,su⟩)),(mono (by norm_num : (1.6500:ℝ) ∈ Ici 0)
    (sqrt_nonneg _) (le_sqrt_of_sq_le sl)).trans hi⟩

/-- Novelty item 7 as an implication from the descriptive table. Each
instrument uses paired pre/post records for 42 pupils per class. The
hypotheses contain no fitted coefficients, test probabilities or ranks. -/
theorem novelty_seven_from_descriptive (a b : IntegerPair) (c d : PairedGroup)
    (ha : MatchesTable a.paired.summary thinkingControl)
    (hb : MatchesTable b.paired.summary thinkingPuzzles)
    (hc : MatchesTable c.summary numbersControl) (hd : MatchesTable d.summary numbersPuzzles) :
    let A := a.paired.summary
    let B := b.paired.summary
    let C := c.summary
    let D := d.summary
    (A.pre < B.pre ∧ C.pre < D.pre ∧
      welchP (B.pre-A.pre) A.preSD B.preSD < 0.05 ∧ welchP (D.pre-C.pre) C.preSD D.preSD < 0.05) ∧
    (0.05 < welchP (B.post-A.post) A.postSD B.postSD ∧
      C.post < D.post ∧ welchP (D.post-C.post) C.postSD D.postSD < 0.05) ∧
    (|B.gain-A.gain| ≤ 0.06 ∧ |D.gain-C.gain| ≤ 0.54) ∧
    (RoundsTo (fittedGroupContrast a.paired b.paired) 1.03 ∧
      Bounds (fittedGroupContrast c d) 6.2158 6.2401) ∧
    (Bounds (fittedGroupP a.paired b.paired) 0.1010 0.1029 ∧ Bounds (fittedGroupP c d) 0.1081 0.10995) ∧
    (0.05 < fittedGroupP a.paired b.paired ∧ 0.05 < fittedGroupP c d) := by
  obtain ⟨⟨preThinking, preNumbers⟩, ⟨preThinkingP, preNumbersP⟩, post, adjusted, gain⟩ :=
    study_summary_from_paired_scores _ _ _ _ ha hb hc hd
  obtain ⟨thinkingContrast, thinkingP⟩ := thinking_primary_from_descriptive a b ha hb
  obtain ⟨_, _, numbersContrast, _⟩ := numbers_adjustment_from_summaries _ _ hc hd c.summary_gain d.summary_gain
  have numbersP := (numbers_ancova_from_paired_scores c d hc hd).1
  have pos {x y : ℝ} (h : RoundsTo x y) (hy : 1/200 < y) : 0 < x := by
    linarith only [(abs_le.mp h).1,hy]
  obtain ⟨fitThinking, pThinking⟩ := fitted_from_summary a.paired b.paired (pos ha.preSD (by norm_num [thinkingControl]))
  obtain ⟨fitNumbers, pNumbers⟩ := fitted_from_summary c d (pos hc.preSD (by norm_num [numbersControl]))
  dsimp only
  rw [fitThinking, pThinking, fitNumbers, pNumbers]
  exact ⟨⟨preThinking, preNumbers, preThinkingP, preNumbersP⟩, post, gain,
    ⟨thinkingContrast, numbersContrast⟩, ⟨thinkingP, numbersP⟩, adjusted⟩

/-- The inputs to the implication can hold simultaneously on the stated
scales. The witnesses establish consistency of the descriptive inputs. -/
theorem descriptive_inputs_realizable :
    ∃ (a b : IntegerPair) (c d : PairedGroup),
      OnThinkingScale a ∧ OnThinkingScale b ∧ InNumbersScale c ∧ InNumbersScale d ∧
      MatchesTable a.paired.summary thinkingControl ∧ MatchesTable b.paired.summary thinkingPuzzles ∧
      MatchesTable c.summary numbersControl ∧ MatchesTable d.summary numbersPuzzles := by
  obtain ⟨a,b,_,_,report,_,_,_⟩ := thinking_post_ranks_not_determined
  obtain ⟨ha,hb,_,_,_,_,sa,sb⟩ := report
  obtain ⟨c,d,sc,sd,hc,hd,_,_⟩ := numbers_ancova_third_decimal_not_determined.1
  exact ⟨a,b,c,d,sa,sb,sc,sd,ha,hb,hc,hd⟩

end Thesis.StudyANCOVA
