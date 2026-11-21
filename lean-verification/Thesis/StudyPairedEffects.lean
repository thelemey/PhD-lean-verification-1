import Thesis.NumbersANCOVA
import Thesis.StudyPairedGains

open Real

namespace Thesis.StudyANCOVA

/-- The paired effect size d_z is the mean individual change divided by
the sample SD of those same changes. -/
noncomputable def pairedEffect (g : PairedGroup) := g.summary.gain/g.summary.gainSD

private theorem standardized_gain (g : PairedGroup) (m s : ℚ)
    (hm : RoundsTo g.summary.gain (m:ℝ)) (hs : RoundsTo g.summary.gainSD (s:ℝ))
    (hm₀ : 0 ≤ m-1/200) (hs₀ : 0 < s-1/200) :
    Bounds (pairedEffect g) ((m-1/200)/(s+1/200)) ((m+1/200)/(s-1/200)) :=
  (Bounds.of_rounding m hm).div (Bounds.of_rounding s hs) hm₀ hs₀

private theorem paired_statistic (g : PairedGroup) {l u : ℚ} (h : Bounds (pairedEffect g) l u)
    (p : 0 ≤ l) :
    Bounds (pairedT (fun i => g.post i-g.pre i)) (l*6.4807406) (u*6.4807407) := by
  have root : Bounds (sqrt 42) 6.4807406 6.4807407 := by
    exact ⟨le_sqrt_of_sq_le (by norm_num),sqrt_le_iff.2 ⟨by norm_num,by norm_num⟩⟩
  have e : pairedT (fun i => g.post i-g.pre i) = pairedEffect g*sqrt 42 := by
    unfold pairedT pairedEffect PairedGroup.summary
    dsimp only
    ring
  rw [e]
  exact h.mul root p (by decide +kernel)

/-- All four displayed standardized within-group gains in §4.3 follow
from the descriptive table alone, at the respective printed precisions. -/
theorem study_paired_effect_sizes (A B C D : PairedGroup)
    (hA : MatchesTable A.summary thinkingControl) (hB : MatchesTable B.summary thinkingPuzzles)
    (hC : MatchesTable C.summary numbersControl) (hD : MatchesTable D.summary numbersPuzzles) :
    |pairedEffect A-1.5| ≤ 1/20 ∧ |pairedEffect B-1.5| ≤ 1/20 ∧
    RoundsTo (pairedEffect C) 0.83 ∧ RoundsTo (pairedEffect D) 0.93 ∧
    RoundsTo (pairedT (fun i => C.post i-C.pre i)) 5.40 ∧
    Bounds (pairedT (fun i => D.post i-D.pre i)) 6.0122 6.0187 := by
  have a := standardized_gain A 5.55 3.62 hA.gain hA.gainSD (by decide +kernel) (by decide +kernel)
  have b := standardized_gain B 5.50 3.58 hB.gain hB.gainSD (by decide +kernel) (by decide +kernel)
  have c := standardized_gain C 17.57 21.08 hC.gain hC.gainSD (by decide +kernel) (by decide +kernel)
  have d := standardized_gain D 18.10 19.50 hD.gain hD.gainSD (by decide +kernel) (by decide +kernel)
  have tenth {x : ℝ} (h : Bounds x 1.45 1.55) : |x-1.5| ≤ 1/20 := by
    obtain ⟨l,u⟩ := h
    simp only [Rat.cast_ofScientific] at l u
    exact abs_le.2 ⟨by linarith only [l],by linarith only [u]⟩
  exact ⟨tenth (a.widen (by decide +kernel) (by decide +kernel)),
    tenth (b.widen (by decide +kernel) (by decide +kernel)),
    c.rounds 0.83 (by decide +kernel) (by decide +kernel),d.rounds 0.93 (by decide +kernel) (by decide +kernel),
    (paired_statistic C c (by decide +kernel)).rounds 5.40 (by decide +kernel) (by decide +kernel),
    (paired_statistic D d (by decide +kernel)).widen (by decide +kernel) (by decide +kernel)⟩

end Thesis.StudyANCOVA
