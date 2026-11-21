import Thesis.StudentOddDegrees
import Thesis.StudentDegreesComparison
import Thesis.ThinkingANCOVA

open Real Set MeasureTheory intervalIntegral

namespace Thesis.StudyANCOVA

private def cubic (x : ℚ) := x - x^3/3
private def quintic (x : ℚ) := cubic x + x^5/5

/-- Exact-rational enclosure for a Student comparison at a rational
multiple of its scale, for any odd degrees of freedom. -/
theorem odd_reference_scaled (n : ℕ) {d : ℝ} (hd : 0 < d) (hs : d^2 = 2*n+1)
    (x l u : ℚ) (hx : 0 ≤ x) (hl : l ≤ 1) (hu : u ≤ 1)
    (lower : studentReduction x (quintic x) n ≤ (1-l)*studentReduction 0 (3.141592/2) n)
    (upper : (1-u)*studentReduction 0 (3.141593/2) n ≤ studentReduction x (cubic x) n) :
    (l:ℝ) ≤ studentTwoSidedP (2*n+1) (d*(x:ℝ)) ∧
      studentTwoSidedP (2*n+1) (d*(x:ℝ)) ≤ (u:ℝ) := by
  let M := studentReduction (0:ℝ) (π/2) n
  let A := studentReduction (x:ℝ) (arctan (x:ℝ)) n
  have hx' : 0 ≤ (x:ℝ) := by exact_mod_cast hx
  have hl' : (l:ℝ) ≤ 1 := by exact_mod_cast hl
  have hu' : (u:ℝ) ≤ 1 := by exact_mod_cast hu
  have loπ := reduction_mono_base n 0 (show (3.141592:ℝ)/2 ≤ π/2 by linarith only [pi_gt_d6])
  have hiπ := reduction_mono_base n 0 (show π/2 ≤ (3.141593:ℝ)/2 by linarith only [pi_lt_d6])
  change _ ≤ M at loπ
  change M ≤ _ at hiπ
  have positive (k : ℕ) : 0 < studentReduction (0:ℝ) (π/2) k := by
    induction k with
    | zero => exact half_pos pi_pos
    | succ k ih =>
      simp only [studentReduction, zero_div, add_zero]
      positivity
  have massPos : 0 < M := positive n
  obtain ⟨loA,hiA⟩ := arctan_cubic_quintic hx'
  have lowA := reduction_mono_base n (x:ℝ) loA
  have highA := reduction_mono_base n (x:ℝ) hiA
  change _ ≤ A at lowA
  change A ≤ _ at highA
  have ha : A ≤ (1-(l:ℝ))*M := by
    apply highA.trans
    apply le_trans _ (mul_le_mul_of_nonneg_left loπ (sub_nonneg.2 hl'))
    have h := (Rat.cast_le (K := ℝ)).2 lower
    simpa only [ratCast_reduction, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_zero,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, quintic, cubic, Rat.cast_add, Rat.cast_ofScientific] using h
  have hb : (1-(u:ℝ))*M ≤ A := by
    apply (mul_le_mul_of_nonneg_left hiπ (sub_nonneg.2 hu')).trans
    apply le_trans _ lowA
    have h := (Rat.cast_le (K := ℝ)).2 upper
    simpa only [ratCast_reduction, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_zero,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, cubic, Rat.cast_ofScientific] using h
  have he := studentTwoSidedP_odd n hd hs (d*(x:ℝ))
  rw [abs_of_nonneg (mul_nonneg hd.le hx'), mul_div_cancel_left₀ _ hd.ne'] at he
  change studentTwoSidedP _ _ = 1-A/M at he
  rw [he]
  exact ⟨by linarith only [(div_le_iff₀ massPos).2 ha], by linarith only [(le_div_iff₀ massPos).2 hb]⟩

/-- For the 81 residual degrees of freedom the scale is exactly 9. Each
comparison below is a decision on rationals after substituting the proved
bounds for arctan and π in the reduction of the Student integral. -/
theorem reference81 (t l u : ℚ) (ht : 0 ≤ t) (hl : l ≤ 1) (hu : u ≤ 1)
    (lower : studentReduction (t/9) (quintic (t/9)) 40 ≤
      (1-l) * studentReduction 0 (3.141592/2) 40)
    (upper : (1-u) * studentReduction 0 (3.141593/2) 40 ≤
      studentReduction (t/9) (cubic (t/9)) 40) :
    (l : ℝ) ≤ studentTwoSidedP 81 (t : ℝ) ∧ studentTwoSidedP 81 (t : ℝ) ≤ (u : ℝ) := by
  have h := odd_reference_scaled 40 (d := 9) (by norm_num) (by norm_num) (t/9) l u
    (div_nonneg ht (by norm_num)) hl hu lower upper
  norm_num only [Nat.cast_ofNat, Rat.cast_div, Rat.cast_ofNat, show (2*40+1:ℝ)=81 by norm_num] at h
  rwa [show 9*((t:ℝ)/9) = (t:ℝ) by ring] at h

private theorem strictAnti_reference81 : StrictAntiOn (studentTwoSidedP 81) (Ici (0:ℝ)) :=
  studentProbability_strictAnti (by norm_num)

private theorem critical95_straddle :
    0.05 < studentTwoSidedP 81 1.989 ∧ studentTwoSidedP 81 1.991 < 0.05 := by
  have hlo := (reference81 1.989 0.05007 0.05015 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).1
  have hhi := (reference81 1.991 0.04984 0.04992 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlo hhi
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

/-- The two-sided Student critical value used for a 95% interval is unique
and lies between the displayed rational endpoints. -/
theorem critical95_df81 :
    ∃! c : ℝ, 0 ≤ c ∧ studentTwoSidedP 81 c = 0.05 := by
  obtain ⟨hlo,hhi⟩ := critical95_straddle
  have cont := continuous_studentProbability (v := 81) (by norm_num)
  have hmem : (0.05:ℝ) ∈ Icc (studentTwoSidedP 81 1.991) (studentTwoSidedP 81 1.989) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨c,hc,he⟩ := isPreconnected_Icc.intermediate_value
    (s := Icc (1.989:ℝ) 1.991) (by norm_num : (1.991:ℝ) ∈ Icc 1.989 1.991)
    (by norm_num : (1.989:ℝ) ∈ Icc 1.989 1.991) cont.continuousOn hmem
  have hc' : 0 ≤ c := (by norm_num : (0:ℝ) ≤ 1.989).trans hc.1
  exact ⟨c, ⟨hc',he⟩, fun v hv => strictAnti_reference81.injOn hv.1 hc' (hv.2.trans he.symm)⟩

noncomputable def critical95 : ℝ := critical95_df81.exists.choose

theorem critical95_spec : 0 ≤ critical95 ∧ studentTwoSidedP 81 critical95 = 0.05 :=
  critical95_df81.exists.choose_spec

theorem critical95_bounds : 1.989 ≤ critical95 ∧ critical95 ≤ 1.991 := by
  obtain ⟨hlo,hhi⟩ := critical95_straddle
  have hc := critical95_spec
  have hm : critical95 ∈ Ici (0:ℝ) := hc.1
  constructor
  · apply le_of_not_gt
    intro h
    have h' := strictAnti_reference81 hm (by norm_num : (1.989:ℝ) ∈ Ici 0) h
    linarith only [hc.2, hlo, h']
  · apply le_of_not_gt
    intro h
    have := strictAnti_reference81 (by norm_num : (1.991:ℝ) ∈ Ici 0) hm h
    linarith only [hc.2, hhi, this]

/-- The complete main ANCOVA row for the twelve-point instrument. The
reported adjusted p and both confidence limits follow from the descriptive
table and the two within-group paired statistics, without assuming any of
the adjusted results as input. -/
theorem thinking_ancova_probability_and_interval (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles)
    (htA : RoundsTo (pairedT (realScores A.gain)) 9.92)
    (htB : RoundsTo (pairedT (realScores B.gain)) 9.97) :
    let a := A.paired.summary
    let b := B.paired.summary
    let g := ancovaContrast a b
    let se := sqrt (ancovaStandardErrorSq a b)
    |ancovaP a b - 0.102| ≤ 1/2000 ∧
    RoundsTo (g-critical95*se) (-0.21) ∧ RoundsTo (g+critical95*se) 2.27 := by
  obtain ⟨hg,hs,ht⟩ := thinking_exact_ancova A B hA hB htA htB
  obtain ⟨cl,cu⟩ := critical95_bounds
  have se₁ := le_sqrt_of_sq_le (by norm_num : (0.6233:ℝ)^2 ≤ 259962180995/669110912064)
  have se₂ := sqrt_le_iff.2 ⟨by norm_num, (by norm_num : (259962180995:ℝ)/669110912064 ≤ 0.6234^2)⟩
  have w₁ := mul_le_mul cl se₁ (by norm_num) (by linarith : 0 ≤ critical95)
  have w₂ := mul_le_mul cu se₂ (sqrt_nonneg _) (by norm_num)
  have tl := le_sqrt_of_sq_le (by norm_num : (1.6542:ℝ)^2 ≤ 142276519845/51992436199)
  have tu := sqrt_le_iff.2 ⟨by norm_num, (by norm_num : (142276519845:ℝ)/51992436199 ≤ 1.6543^2)⟩
  have p₁ := (reference81 1.6543 0.10193 0.10197 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  have p₂ := (reference81 1.6542 0.10195 0.10199 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at p₁ p₂
  have pm₁ := strictAnti_reference81.antitoneOn (sqrt_nonneg _) (by norm_num : (1.6543:ℝ) ∈ Ici 0) tu
  have pm₂ := strictAnti_reference81.antitoneOn (by norm_num : (1.6542:ℝ) ∈ Ici 0) (sqrt_nonneg _) tl
  dsimp only
  rw [ancovaP, ht, hg, hs]
  exact ⟨abs_le.2 ⟨by linarith only [p₁,pm₁], by linarith only [p₂,pm₂]⟩,
    abs_le.2 ⟨by linarith only [w₂], by linarith only [w₁]⟩,
    abs_le.2 ⟨by linarith only [w₁], by linarith only [w₂]⟩⟩

/-- For the hundred-point instrument, the separately reported 95% interval
and group contrast determine the printed p at its own precision. The
assumptions make this a cross-check of those columns of the ANCOVA table. -/
theorem numbers_ancova_probability_of_interval {g se : ℝ} (hs : 0 < se)
    (hg : RoundsTo g 6.23) (hl : RoundsTo (g-critical95*se) (-1.42))
    (hu : RoundsTo (g+critical95*se) 13.87) :
    |studentTwoSidedP 81 (g/se) - 0.109| ≤ 1/2000 := by
  obtain ⟨cl,cu⟩ := critical95_bounds
  obtain ⟨gl,gu⟩ := abs_le.mp hg
  obtain ⟨ll,lu⟩ := abs_le.mp hl
  obtain ⟨ul,uu⟩ := abs_le.mp hu
  have lower : 1.61849 ≤ g/se := by
    apply (le_div_iff₀ hs).2
    linarith only [mul_le_mul_of_nonneg_right cl hs.le, gl, ll, uu]
  have upper : g/se ≤ 1.6226 := by
    apply (div_le_iff₀ hs).2
    linarith only [mul_le_mul_of_nonneg_right cu hs.le, lu, uu]
  have p₁ := (reference81 1.6226 0.10855 0.10859 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  have p₂ := (reference81 1.61849 0.10944 0.10948 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at p₁ p₂
  have hg' : g/se ∈ Ici (0:ℝ) := (by norm_num : (0:ℝ) ≤ 1.61849).trans lower
  have pm₁ := strictAnti_reference81.antitoneOn hg' (by norm_num : (1.6226:ℝ) ∈ Ici 0) upper
  have pm₂ := strictAnti_reference81.antitoneOn (by norm_num : (1.61849:ℝ) ∈ Ici 0) hg' lower
  exact abs_le.2 ⟨by linarith only [p₁,pm₁], by linarith only [p₂,pm₂]⟩

end Thesis.StudyANCOVA
