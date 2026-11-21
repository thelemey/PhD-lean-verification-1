import Thesis.StudyCriticalValues

open Real Set

namespace Thesis.StudyANCOVA
set_option maxHeartbeats 1200000

/-- The pre and post integer sums forced by the descriptive table give the
two Welch statistics and their unrounded Satterthwaite degrees of freedom. -/
theorem thinking_welch_exact (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles) :
    let a := A.paired.summary
    let b := B.paired.summary
    welchSquared (b.pre-a.pre) (withinSS a.preSD b.preSD) = 4961/1082 ∧
    welchDF a.preSD b.preSD = 95999368/1173749 ∧
    welchSquared (b.post-a.post) (withinSS a.postSD b.postSD) = 36162/13151 ∧
    welchDF a.postSD b.postSD = 14181801682/174051301 := by
  obtain ⟨⟨sa,qa⟩,⟨ta,ra⟩,_,⟨sb,qb⟩,⟨tb,rb⟩,_⟩ := thinking_integer_moments A B hA hB
  have fourth (x : ℝ) : x^4 = (x^2)^2 := by ring
  dsimp only [PairedGroup.summary, IntegerPair.paired]
  norm_num [welchSquared, withinSS, welchDF, fourth, sampleSD_sq, mean_integer,
    ss_integer, momentSS, sa,qa,ta,ra,sb,qb,tb,rb]

private theorem bound_welch_probability {v s x y l u : ℝ}
    (hv : 81 ≤ v) (hv' : v ≤ 83) (hs : 1.5^2 ≤ s)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h81 : 81*x^2 ≤ s) (h83 : s ≤ 83*y^2)
    (hL : l ≤ studentTwoSidedP 83 (sqrt 83*y))
    (hU : studentTwoSidedP 81 (9*x) ≤ u) :
    l ≤ studentTwoSidedP v (sqrt s) ∧ studentTwoSidedP v (sqrt s) ≤ u := by
  have ht := le_sqrt_of_sq_le hs
  have hl : 9*x ≤ sqrt s := le_sqrt_of_sq_le (by nlinarith only [h81])
  have hu : sqrt s ≤ sqrt 83*y := sqrt_le_iff.2 ⟨mul_nonneg (sqrt_nonneg _) hy, by
    rw [mul_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 83)]
    exact h83⟩
  have mL := (studentProbability_strictAnti (v := 83) (by norm_num)).antitoneOn
    (sqrt_nonneg _) (mul_nonneg (sqrt_nonneg _) hy) hu
  have mU := (studentProbability_strictAnti (v := 81) (by norm_num)).antitoneOn
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 9) hx) (sqrt_nonneg _) hl
  exact ⟨hL.trans (mL.trans (student_probability_antitone_degrees (by linarith) hv' ht)),
    (student_probability_antitone_degrees (by norm_num) hv ht).trans (mU.trans hU)⟩

/-- Reproduction of both unadjusted Welch p values at the precision printed
in §4.3, using only the integer scores and the descriptive table. -/
theorem thinking_welch_probabilities (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles) :
    let a := A.paired.summary
    let b := B.paired.summary
    |welchP (b.pre-a.pre) a.preSD b.preSD - 0.035| ≤ 1/2000 ∧
    |welchP (b.post-a.post) a.postSD b.postSD - 0.101| ≤ 1/2000 := by
  obtain ⟨ts,ds,tt,dt⟩ := thinking_welch_exact A B hA hB
  have preHi := (odd_reference_scaled 40 (d := 9) (by norm_num) (by norm_num) 0.2379 0.03526 0.03537
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2
  have preLo := (odd_reference_scaled 41 (d := sqrt 83) (by positivity) (by norm_num) 0.2351 0.03513 0.03523
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  have postHi := (odd_reference_scaled 40 (d := 9) (by norm_num) (by norm_num) 0.18424 0.10115 0.10119
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2
  have postLo := (odd_reference_scaled 41 (d := sqrt 83) (by positivity) (by norm_num) 0.18204 0.10099 0.10103
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  simp only [Nat.cast_ofNat, Rat.cast_ofScientific, show (2*40+1:ℝ)=81 by norm_num,
    show (2*41+1:ℝ)=83 by norm_num] at preHi preLo postHi postLo
  obtain ⟨pl,pu⟩ := bound_welch_probability (v := 95999368/1173749) (s := 4961/1082)
    (x := 0.2379) (y := 0.2351) (l := 0.03513) (u := 0.03537)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) preLo preHi
  obtain ⟨ql,qu⟩ := bound_welch_probability (v := 14181801682/174051301) (s := 36162/13151)
    (x := 0.18424) (y := 0.18204) (l := 0.10099) (u := 0.10119)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) postLo postHi
  dsimp only
  unfold welchP
  rw [ts,ds,tt,dt,abs_le,abs_le]
  exact ⟨⟨by linarith only [pl], by linarith only [pu]⟩,
    ⟨by linarith only [ql], by linarith only [qu]⟩⟩


/-- For each real Welch degree in this range the unique two-sided 95%
critical value is between 1.988 and 1.991. -/
theorem welch_critical95_bounds {v : ℝ} (hv : 81 ≤ v) (hv' : v ≤ 83) :
    ∃ c ∈ Icc (1.988:ℝ) 1.991, studentTwoSidedP v c = 0.05 ∧
      ∀ z, 0 ≤ z → studentTwoSidedP v z = 0.05 → z = c := by
  have lo := (odd_reference_scaled 41 (d := sqrt 83) (by positivity) (by norm_num)
    0.21822 0.05009 0.05017 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).1
  have hi := (odd_reference_scaled 40 (d := 9) (by norm_num) (by norm_num)
    0.2212 0.04987 0.04995 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2
  simp only [Nat.cast_ofNat, Rat.cast_ofScientific, show (2*40+1:ℝ)=81 by norm_num,
    show (2*41+1:ℝ)=83 by norm_num] at lo hi
  have hs := le_sqrt_of_sq_le (by norm_num : (9.11043:ℝ)^2 ≤ 83)
  have hL := (studentProbability_strictAnti (v := 83) (by norm_num)).antitoneOn
    (by norm_num : (1.988:ℝ) ∈ Ici 0) (by change 0 ≤ sqrt 83 * 0.21822; positivity)
    (by linarith only [hs] : 1.988 ≤ sqrt 83 * 0.21822)
  have hU := (studentProbability_strictAnti (v := 81) (by norm_num)).antitoneOn
    (by norm_num : (9*0.2212:ℝ) ∈ Ici 0) (by norm_num : (1.991:ℝ) ∈ Ici 0) (by norm_num)
  have sL := student_probability_antitone_degrees (by linarith : 79 ≤ v) hv' (by norm_num : (1.5:ℝ) ≤ 1.988)
  have sU := student_probability_antitone_degrees (by norm_num : (79:ℝ) ≤ 81) hv (by norm_num : (1.5:ℝ) ≤ 1.991)
  have hmem : (0.05:ℝ) ∈ Icc (studentTwoSidedP v 1.991) (studentTwoSidedP v 1.988) :=
    ⟨by linarith only [hi,hU,sU], by linarith only [lo,hL,sL]⟩
  obtain ⟨c,hc,he⟩ := isPreconnected_Icc.intermediate_value
    (s := Icc (1.988:ℝ) 1.991) (by norm_num : (1.991:ℝ) ∈ Icc 1.988 1.991)
    (by norm_num : (1.988:ℝ) ∈ Icc 1.988 1.991)
    (continuous_studentProbability (by linarith : 1 ≤ v)).continuousOn hmem
  exact ⟨c,hc,he, fun z hz he' => (studentProbability_strictAnti (by linarith : 1 ≤ v)).injOn
    hz ((by norm_num : (0:ℝ) ≤ 1.988).trans hc.1) (he'.trans he.symm)⟩

/-- Both limits of a 95% Welch confidence interval, computed with the
unrounded mean contrast and standard error. -/
def WelchInterval (difference pooled df low high : ℝ) : Prop :=
  ∃ c, 0 ≤ c ∧ studentTwoSidedP df c = 0.05 ∧
    RoundsTo (difference-c*sqrt (pooled/(41*42))) low ∧
    RoundsTo (difference+c*sqrt (pooled/(41*42))) high

private theorem rounded_welch_interval {d S v low high l u : ℝ} (hv : 81 ≤ v) (hv' : v ≤ 83)
    (hl : 0 ≤ l) (hu : 0 ≤ u) (hls : l^2 ≤ S/(41*42)) (hus : S/(41*42) ≤ u^2)
    (ll : low-1/200 ≤ d-1.991*u) (lu : d-1.988*l ≤ low+1/200)
    (ul : high-1/200 ≤ d+1.988*l) (uu : d+1.991*u ≤ high+1/200) :
    WelchInterval d S v low high := by
  obtain ⟨c,hc,he,_⟩ := welch_critical95_bounds hv hv'
  have hc' : 0 ≤ c := (by norm_num : (0:ℝ) ≤ 1.988).trans hc.1
  have w₁ := mul_le_mul hc.1 (le_sqrt_of_sq_le hls) hl hc'
  have w₂ := mul_le_mul hc.2 (sqrt_le_iff.2 ⟨hu,hus⟩) (sqrt_nonneg _) (by norm_num)
  exact ⟨c,hc',he,abs_le.2 ⟨by linarith only [ll,w₂], by linarith only [lu,w₁]⟩,
    abs_le.2 ⟨by linarith only [ul,w₁], by linarith only [uu,w₂]⟩⟩

/-- The two confidence intervals in the corrected text follow independently
from the descriptive table and the 42 integer scores in each group. -/
theorem thinking_welch_intervals (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles) :
    let a := A.paired.summary
    let b := B.paired.summary
    WelchInterval (b.pre-a.pre) (withinSS a.preSD b.preSD) (welchDF a.preSD b.preSD) 0.07 2.02 ∧
    WelchInterval (b.post-a.post) (withinSS a.postSD b.postSD) (welchDF a.postSD b.postSD) (-0.20) 2.20 := by
  obtain ⟨_,ds,_,dt⟩ := thinking_welch_exact A B hA hB
  obtain ⟨⟨sa,qa⟩,⟨ta,ra⟩,_,⟨sb,qb⟩,⟨tb,rb⟩,_⟩ := thinking_integer_moments A B hA hB
  dsimp only
  rw [ds,dt]
  dsimp only [PairedGroup.summary,IntegerPair.paired]
  norm_num only [mean_integer,withinSS_sampleSD,ss_integer,momentSS,sa,qa,ta,ra,sb,qb,tb,rb,Int.cast_ofNat]
  constructor
  · apply rounded_welch_interval (l := 0.4892517) (u := 0.4892518) <;> norm_num
  · apply rounded_welch_interval (l := 0.6030497) (u := 0.6030498) <;> norm_num


private theorem round_sqrt {x target : ℝ} (hu : 0 ≤ target+1/200)
    (hl : (target-1/200)^2 ≤ x) (hh : x ≤ (target+1/200)^2) :
    RoundsTo (sqrt x) target := by
  exact abs_le.2 ⟨by linarith only [le_sqrt_of_sq_le hl], by linarith only [sqrt_le_iff.2 ⟨hu,hh⟩]⟩

/-- Cohen's standardized difference uses the pooled within-group variance
with 82 degrees of freedom. -/
noncomputable def pooledCohenD (d S : ℝ) : ℝ := d/sqrt (S/82)

private theorem round_effect {d S target l u : ℝ} (hl : 0 < l) (hu : 0 ≤ u)
    (ls : l^2 ≤ S/82) (us : S/82 ≤ u^2) (ht : 0 ≤ target-1/200)
    (lo : (target-1/200)*u ≤ d) (hi : d ≤ (target+1/200)*l) : RoundsTo (pooledCohenD d S) target := by
  have sl := le_sqrt_of_sq_le ls
  have su := sqrt_le_iff.2 ⟨hu,us⟩
  have l' := (le_div_iff₀ (hl.trans_le sl)).2 ((mul_le_mul_of_nonneg_left su ht).trans lo)
  have u' := (div_le_iff₀ (hl.trans_le sl)).2 (hi.trans (mul_le_mul_of_nonneg_left sl (by linarith)))
  unfold pooledCohenD
  exact abs_le.2 ⟨by linarith only [l'], by linarith only [u']⟩

theorem thinking_welch_displayed_statistics (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles) :
    let a := A.paired.summary
    let b := B.paired.summary
    let x := withinSS a.preSD b.preSD
    let y := withinSS a.postSD b.postSD
    RoundsTo (b.pre-a.pre) 1.05 ∧ RoundsTo (b.post-a.post) 1.00 ∧
    RoundsTo (sqrt (welchSquared (b.pre-a.pre) x)) 2.14 ∧
    RoundsTo (sqrt (welchSquared (b.post-a.post) y)) 1.66 ∧
    |welchDF a.preSD b.preSD-81.8| ≤ 1/20 ∧ |welchDF a.postSD b.postSD-81.5| ≤ 1/20 ∧
    RoundsTo (pooledCohenD (b.pre-a.pre) x) 0.47 ∧ RoundsTo (pooledCohenD (b.post-a.post) y) 0.36 := by
  obtain ⟨ts,ds,tt,dt⟩ := thinking_welch_exact A B hA hB
  obtain ⟨⟨sa,qa⟩,⟨ta,ra⟩,_,⟨sb,qb⟩,⟨tb,rb⟩,_⟩ := thinking_integer_moments A B hA hB
  dsimp only
  rw [ts,tt,ds,dt]
  dsimp only [PairedGroup.summary,IntegerPair.paired]
  simp only [mean_integer,withinSS_sampleSD,ss_integer,momentSS,sa,qa,ta,ra,sb,qb,tb,rb,Int.cast_ofNat]
  refine ⟨by norm_num [RoundsTo,abs_le],by norm_num [RoundsTo,abs_le],?_,?_,
    by norm_num [abs_le],by norm_num [abs_le],?_,?_⟩
  · apply round_sqrt <;> norm_num
  · apply round_sqrt <;> norm_num
  · apply round_effect (l := 2.2420) (u := 2.2421) <;> norm_num
  · apply round_effect (l := 2.7635) (u := 2.7636) <;> norm_num

end Thesis.StudyANCOVA
