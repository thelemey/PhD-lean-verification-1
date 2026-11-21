import Thesis.StudyANCOVATable
import Thesis.StudyReferenceBounds

namespace Thesis.StudyANCOVA

/-- One row of the descriptive table, including paired gains. -/
structure GroupSummary where
  pre : ℝ
  post : ℝ
  gain : ℝ
  preSD : ℝ
  postSD : ℝ
  gainSD : ℝ

/-- Rounding is applied to each printed entry separately. -/
structure MatchesTable (actual printed : GroupSummary) : Prop where
  pre : RoundsTo actual.pre printed.pre
  post : RoundsTo actual.post printed.post
  gain : RoundsTo actual.gain printed.gain
  preSD : RoundsTo actual.preSD printed.preSD
  postSD : RoundsTo actual.postSD printed.postSD
  gainSD : RoundsTo actual.gainSD printed.gainSD

noncomputable def thinkingControl : GroupSummary := ⟨2.71, 8.26, 5.55, 2.30, 2.87, 3.62⟩
noncomputable def thinkingPuzzles : GroupSummary := ⟨3.76, 9.26, 5.50, 2.18, 2.65, 3.58⟩
noncomputable def numbersControl : GroupSummary := ⟨47.79, 65.36, 17.57, 24.68, 21.61, 21.08⟩
noncomputable def numbersPuzzles : GroupSummary := ⟨59.74, 77.83, 18.10, 22.11, 20.19, 19.50⟩

/-- Welch–Satterthwaite degrees of freedom for two groups of 42. -/
noncomputable def welchDF (a b : ℝ) : ℝ := 41 * (a ^ 2 + b ^ 2) ^ 2 / (a ^ 4 + b ^ 4)

theorem welchDF_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : 6*a ≤ 7*b) (hba : 6*b ≤ 7*a) : 80 ≤ welchDF a b ∧ welchDF a b ≤ 82 := by
  have h₁ := pow_le_pow_left₀ (by positivity : 0 ≤ 6*a) hab 2
  have h₂ := pow_le_pow_left₀ (by positivity : 0 ≤ 6*b) hba 2
  have h₃ : 0 ≤ 49*a^2 - 36*b^2 := by linarith only [h₂]
  have h₄ : 0 ≤ 49*b^2 - 36*a^2 := by linarith only [h₁]
  have hs := mul_nonneg h₃ h₄
  have hden : 0 < a^4 + b^4 := by positivity
  unfold welchDF
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith only [hs, sq_nonneg (a^2+b^2)]
  · apply (div_le_iff₀ hden).2
    nlinarith only [sq_nonneg (a^2-b^2)]

private theorem welchDF_of_rounding {a b a₀ b₀ : ℝ}
    (ha : RoundsTo a a₀) (hb : RoundsTo b b₀)
    (ha₀ : 1/200 < a₀) (hb₀ : 1/200 < b₀)
    (hab : 6*(a₀+1/200) ≤ 7*(b₀-1/200))
    (hba : 6*(b₀+1/200) ≤ 7*(a₀-1/200)) : 80 ≤ welchDF a b ∧ welchDF a b ≤ 82 := by
  obtain ⟨hal, hau⟩ := abs_le.mp ha
  obtain ⟨hbl, hbu⟩ := abs_le.mp hb
  apply welchDF_bounds (by linarith only [ha₀, hal]) (by linarith only [hb₀, hbl]) <;> linarith

noncomputable def welchP (contrast a b : ℝ) : ℝ :=
  studentTwoSidedP (welchDF a b) (Real.sqrt (welchSquared contrast (withinSS a b)))

noncomputable def ancovaSquaredT (A B : GroupSummary) : ℝ :=
  let xx := withinSS A.preSD B.preSD
  let yy := withinSS A.postSD B.postSD
  let xy := (xx + yy - withinSS A.gainSD B.gainSD) / 2
  squaredT (B.pre-A.pre) (B.post-A.post) xx yy xy

noncomputable def ancovaP (A B : GroupSummary) : ℝ :=
  studentTwoSidedP 81 (Real.sqrt (ancovaSquaredT A B))

theorem p_gt_five_percent {ν t₂ : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82)
    (ht : t₂ < (1.8 : ℝ)^2) : 0.05 < studentTwoSidedP ν (Real.sqrt t₂) := by
  apply (study_student_p_cutoffs hν hν').1
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num, ht.le⟩)

private theorem p_lt_five_percent {ν t₂ : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82)
    (ht : (2.1 : ℝ)^2 ≤ t₂) : studentTwoSidedP ν (Real.sqrt t₂) < 0.05 := by
  apply (study_student_p_cutoffs hν hν').2
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.le_sqrt_of_sq_le ht

/-- The thinking instrument. The pre-test contrast is significant, and the
unadjusted post-test and common-slope ANCOVA contrasts are both nonsignificant.
The mean gains differ by at most 0.06 on the twelve-point scale. -/
theorem thinking_study_decisions {A B : GroupSummary}
    (hA : MatchesTable A thinkingControl) (hB : MatchesTable B thinkingPuzzles) :
    welchP (B.pre-A.pre) A.preSD B.preSD < 0.05 ∧
    0.05 < welchP (B.post-A.post) A.postSD B.postSD ∧
    0.05 < ancovaP A B ∧ |B.gain-A.gain| ≤ 0.06 := by
  have hx : |(B.pre-A.pre)-1.05| ≤ 1/100 := by
    convert difference_rounding hA.pre hB.pre using 1
    norm_num [thinkingControl, thinkingPuzzles]
  have hy : |(B.post-A.post)-1.00| ≤ 1/100 := by
    convert difference_rounding hA.post hB.post using 1
    norm_num [thinkingControl, thinkingPuzzles]
  have hwp := thinking_welch_enclosure hx hy hA.preSD hB.preSD hA.postSD hB.postSD
  have hanc := thinking_ancova_enclosure hx hy hA.preSD hB.preSD hA.postSD hB.postSD hA.gainSD hB.gainSD
  have df₁ := welchDF_of_rounding hA.preSD hB.preSD (by norm_num [thinkingControl])
    (by norm_num [thinkingPuzzles]) (by norm_num [thinkingControl, thinkingPuzzles])
    (by norm_num [thinkingControl, thinkingPuzzles])
  have df₂ := welchDF_of_rounding hA.postSD hB.postSD (by norm_num [thinkingControl])
    (by norm_num [thinkingPuzzles]) (by norm_num [thinkingControl, thinkingPuzzles])
    (by norm_num [thinkingControl, thinkingPuzzles])
  refine ⟨p_lt_five_percent df₁.1 df₁.2 hwp.1.le, p_gt_five_percent df₂.1 df₂.2 hwp.2,
    p_gt_five_percent (by norm_num) (by norm_num)
      (by simpa only [ancovaSquaredT, show (1.8 : ℝ) = 9 / 5 by norm_num] using hanc.2.2), ?_⟩
  obtain ⟨hl, hu⟩ := abs_le.mp (difference_rounding hA.gain hB.gain)
  norm_num [thinkingControl, thinkingPuzzles] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The numbers instrument. Both unadjusted contrasts are significant,
but the baseline-adjusted comparison is nonsignificant. The difference
between mean gains is at most 0.54 on the hundred-point scale. -/
theorem numbers_study_decisions {A B : GroupSummary}
    (hA : MatchesTable A numbersControl) (hB : MatchesTable B numbersPuzzles) :
    welchP (B.pre-A.pre) A.preSD B.preSD < 0.05 ∧
    welchP (B.post-A.post) A.postSD B.postSD < 0.05 ∧
    0.05 < ancovaP A B ∧ |B.gain-A.gain| ≤ 0.54 := by
  have hx : |(B.pre-A.pre)-11.95| ≤ 1/100 := by
    convert difference_rounding hA.pre hB.pre using 1
    norm_num [numbersControl, numbersPuzzles]
  have hy : |(B.post-A.post)-12.47| ≤ 1/100 := by
    convert difference_rounding hA.post hB.post using 1
    norm_num [numbersControl, numbersPuzzles]
  have hwp := numbers_welch_enclosure hx hy hA.preSD hB.preSD hA.postSD hB.postSD
  have hanc := numbers_ancova_enclosure hx hy hA.preSD hB.preSD hA.postSD hB.postSD hA.gainSD hB.gainSD
  have df₁ := welchDF_of_rounding hA.preSD hB.preSD (by norm_num [numbersControl])
    (by norm_num [numbersPuzzles]) (by norm_num [numbersControl, numbersPuzzles])
    (by norm_num [numbersControl, numbersPuzzles])
  have df₂ := welchDF_of_rounding hA.postSD hB.postSD (by norm_num [numbersControl])
    (by norm_num [numbersPuzzles]) (by norm_num [numbersControl, numbersPuzzles])
    (by norm_num [numbersControl, numbersPuzzles])
  refine ⟨p_lt_five_percent df₁.1 df₁.2 hwp.1.le,
    p_lt_five_percent df₂.1 df₂.2 ((by norm_num : (2.1 : ℝ)^2 ≤ 2.5^2).trans hwp.2.le),
    p_gt_five_percent (by norm_num) (by norm_num)
      (by simpa only [ancovaSquaredT, show (1.8 : ℝ) = 9 / 5 by norm_num] using hanc.2.2), ?_⟩
  obtain ⟨hl, hu⟩ := abs_le.mp (difference_rounding hA.gain hB.gain)
  norm_num [numbersControl, numbersPuzzles] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A group of 42 observations. Both columns use the same pupil index. -/
structure PairedGroup where
  pre : Fin 42 → ℝ
  post : Fin 42 → ℝ

noncomputable def PairedGroup.summary (g : PairedGroup) : GroupSummary :=
  let gain := fun i => g.post i - g.pre i
  ⟨mean g.pre, mean g.post, mean gain, sampleSD g.pre, sampleSD g.post, sampleSD gain⟩

/-- The statistic reconstructed from the descriptive table is the statistic
from the least-squares fit to the paired observations. Its numerator is the
fitted group contrast squared; the denominator uses the actual residual sum
of squares and the contrast variance multiplier of this design. -/
theorem ancovaSquaredT_eq_fitted_statistic (A B : PairedGroup)
    (hx : 0 < ss A.pre + ss B.pre) :
    let xx := ss A.pre + ss B.pre
    let xy := cross A.pre A.post + cross B.pre B.post
    let slope := xy / xx
    let dx := mean B.pre - mean A.pre
    let contrast := mean B.post - mean A.post - slope * dx
    let intercept := mean A.post - slope * mean A.pre
    ancovaSquaredT A.summary B.summary =
      contrast^2 / ((loss A.pre A.post B.pre B.post intercept contrast slope / 81) *
        (2 / 42 + dx^2 / xx)) := by
  dsimp only
  have hfit := loss_at_fit (by decide : 0 < 42) A.pre A.post B.pre B.post hx
  simp only at hfit
  rw [hfit]
  unfold ancovaSquaredT PairedGroup.summary
  have hxy := pooled_cross_of_sampleSD A.pre A.post B.pre B.post
  simp only [withinSS_sampleSD] at hxy
  simp only [withinSS_sampleSD, ← hxy, squaredT, adjustedDifference,
    residualVariance, show (2 / 42 : ℝ) = 1 / 21 by norm_num]

/-- The inferential comparison in novelty item 7 for any paired observations
consistent with the printed means and standard deviations. -/
theorem study_summary_from_paired_scores (thinkingA thinkingB numbersA numbersB : PairedGroup)
    (htA : MatchesTable thinkingA.summary thinkingControl)
    (htB : MatchesTable thinkingB.summary thinkingPuzzles)
    (hnA : MatchesTable numbersA.summary numbersControl)
    (hnB : MatchesTable numbersB.summary numbersPuzzles) :
    let A := thinkingA.summary
    let B := thinkingB.summary
    let C := numbersA.summary
    let D := numbersB.summary
    (A.pre < B.pre ∧ C.pre < D.pre) ∧
    (welchP (B.pre-A.pre) A.preSD B.preSD < 0.05 ∧
      welchP (D.pre-C.pre) C.preSD D.preSD < 0.05) ∧
    (0.05 < welchP (B.post-A.post) A.postSD B.postSD ∧
      C.post < D.post ∧ welchP (D.post-C.post) C.postSD D.postSD < 0.05) ∧
    (0.05 < ancovaP A B ∧ 0.05 < ancovaP C D) ∧
    (|B.gain-A.gain| ≤ 0.06 ∧ |D.gain-C.gain| ≤ 0.54) := by
  dsimp only
  obtain ⟨htx, hty, hta, htg⟩ := thinking_study_decisions htA htB
  obtain ⟨hnx, hny, hna, hng⟩ := numbers_study_decisions hnA hnB
  have htp := abs_le.mp (difference_rounding htA.pre htB.pre)
  have hnp := abs_le.mp (difference_rounding hnA.pre hnB.pre)
  have hns := abs_le.mp (difference_rounding hnA.post hnB.post)
  norm_num [thinkingControl, thinkingPuzzles, numbersControl, numbersPuzzles] at htp hnp hns
  exact ⟨⟨by linarith [htp.1], by linarith [hnp.1]⟩, ⟨htx, hnx⟩,
    ⟨hty, by linarith [hns.1], hny⟩, ⟨hta, hna⟩, htg, hng⟩

end Thesis.StudyANCOVA
