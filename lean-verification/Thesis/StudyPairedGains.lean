import Thesis.ThinkingANCOVA

open Real Set MeasureTheory Filter intervalIntegral

namespace Thesis.StudyANCOVA

private theorem kernel41 (x : ℝ) : studentKernel 41 x = 1/(1+x^2/41)^(21:ℕ) := by
  unfold studentKernel
  rw [show ((41:ℝ)+1)/2 = ((21:ℕ):ℝ) by norm_num, rpow_natCast]

/-- For the paired t tests (41 df), the smallest statistic in the table
already has a two-sided tail below 0.001. The rational tail estimate is
uniform over every statistic of magnitude at least 5.3. -/
theorem paired_probability_cutoff (t : ℝ) (ht : 5.3 ≤ |t|) : studentTwoSidedP 41 t < 0.001 := by
  let c : ℝ := 5.3
  let major := fun x : ℝ => (1/800:ℝ)*x^(-2:ℝ)
  have hc : 0 < c := by norm_num [c]
  have hmajor : IntegrableOn major (Ioi c) := (integrableOn_Ioi_rpow_of_lt (by norm_num) hc).const_mul _
  have bound (x : ℝ) (hx : c ≤ x) : studentKernel 41 x ≤ major x := by
    have hpos := hc.trans_le hx
    have hxx := pow_le_pow_left₀ hc.le hx 2
    have hp : (32800:ℝ) ≤ (1+x^2/41)^20 :=
      (by norm_num [c] : (32800:ℝ) ≤ (1+c^2/41)^20).trans
        (pow_le_pow_left₀ (by positivity) (add_le_add_left (div_le_div_of_nonneg_right hxx (by norm_num : (0:ℝ) ≤ 41)) 1) _)
    have hm := mul_le_mul hp (show x^2/41 ≤ 1+x^2/41 by linarith) (by positivity) (by positivity)
    have hd : 800*x^2 ≤ (1+x^2/41)^21 := by
      rw [show (21:ℕ)=20+1 by decide, pow_succ]
      linarith only [hm]
    rw [kernel41]
    apply (one_div_le_one_div_of_le (by positivity) hd).trans_eq
    simp only [major, rpow_neg hpos.le, show (2:ℝ)=((2:ℕ):ℝ) by norm_num, rpow_natCast]
    ring
  have htail : IntegrableOn (studentKernel 41) (Ioi c) := by
    apply hmajor.mono' (continuous_studentKernel (by norm_num)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioi c) measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (studentKernel_pos (by norm_num) _)]
    exact bound x hx.le
  have nonneg (s : Set ℝ) : 0 ≤ᵐ[volume.restrict s] studentKernel 41 :=
    Eventually.of_forall fun x => (studentKernel_pos (by norm_num) x).le
  have hnum : studentTail 41 |t| ≤ 1/(800*c) := by
    apply (setIntegral_mono_set htail (nonneg _) (ae_of_all _ (fun _ => (Ioi_subset_Ioi ht ·)))).trans
    apply (setIntegral_mono_on htail hmajor measurableSet_Ioi (fun x hx => bound x hx.le)).trans_eq
    simp only [major, MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hc]
    norm_num [c, Real.rpow_neg_one]
  have hpart := (continuous_studentKernel (ν:=41) (by norm_num)).intervalIntegrable (μ:=volume) 0 c
  have hint : IntegrableOn (studentKernel 41) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hc.le]
    exact hpart.1.union htail
  have hden : 1/2 ≤ studentTail 41 0 := by
    have hb (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : 1/2 ≤ studentKernel 41 x := by
      rw [kernel41]
      apply (by norm_num : 1/2 ≤ 1/(1+(1:ℝ)/41)^21).trans
      apply one_div_le_one_div_of_le (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
      linarith
    have hlow := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1) intervalIntegrable_const
      ((continuous_studentKernel (by norm_num)).intervalIntegrable (μ:=volume) 0 1) hb
    rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at hlow
    have hsub := setIntegral_mono_set hint (nonneg _) (ae_of_all _ (show ∀ x : ℝ, x ∈ Ioc 0 1 → x ∈ Ioi 0 from fun _ hx => hx.1))
    norm_num at hlow
    exact hlow.trans hsub
  apply (div_lt_iff₀ (show 0 < studentTail 41 0 by linarith)).2
  dsimp [c] at hnum
  linarith only [hden,hnum]

/-- The within-group comparisons and the Welch tests of between-group
gains in §4.3 follow from the printed paired gain means and SDs alone. -/
theorem study_gain_tests (A B C D : PairedGroup)
    (hA : MatchesTable A.summary thinkingControl) (hB : MatchesTable B.summary thinkingPuzzles)
    (hC : MatchesTable C.summary numbersControl) (hD : MatchesTable D.summary numbersPuzzles) :
    let gains := fun (g : PairedGroup) (i : Fin 42) => g.post i - g.pre i
    (∀ g ∈ [A,B,C,D], studentTwoSidedP 41 (pairedT (gains g)) < 0.001) ∧
    0.05 < welchP (B.summary.gain-A.summary.gain) A.summary.gainSD B.summary.gainSD ∧
    0.05 < welchP (D.summary.gain-C.summary.gain) C.summary.gainSD D.summary.gainSD := by
  intro gains
  have paired (g : PairedGroup) {p : GroupSummary} (h : MatchesTable g.summary p)
      (hm : 1/200 ≤ p.gain) (hs : 1/200 < p.gainSD)
      (check : 5.3 * (p.gainSD+1/200) ≤ (p.gain-1/200)*6.48) :
      studentTwoSidedP 41 (pairedT (gains g)) < 0.001 := by
    obtain ⟨ml,mu⟩ := abs_le.mp h.gain
    obtain ⟨sl,su⟩ := abs_le.mp h.gainSD
    have hs' : 0 < g.summary.gainSD := by linarith
    have root := le_sqrt_of_sq_le (by norm_num : (6.48:ℝ)^2 ≤ 42)
    have hmul := mul_le_mul (by linarith : p.gain-1/200 ≤ g.summary.gain) root (by norm_num) (by linarith)
    apply paired_probability_cutoff
    apply le_trans _ (le_abs_self _)
    change 5.3 ≤ g.summary.gain * sqrt 42 / g.summary.gainSD
    apply (le_div_iff₀ hs').2
    linarith only [hmul, check, su]
  have gain_welch {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (h₁ : 6*a ≤ 7*b) (h₂ : 6*b ≤ 7*a)
      (small : 42*d^2 < (1.8:ℝ)^2 * (a^2+b^2)) : 0.05 < welchP d a b := by
    obtain ⟨lo,hi⟩ := welchDF_bounds ha hb h₁ h₂
    apply p_gt_five_percent lo hi
    unfold welchSquared withinSS
    apply (div_lt_iff₀ (by positivity)).2
    linarith only [small]
  constructor
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact paired _ hA (by norm_num [thinkingControl]) (by norm_num [thinkingControl]) (by norm_num [thinkingControl])
    · exact paired _ hB (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles])
    · exact paired _ hC (by norm_num [numbersControl]) (by norm_num [numbersControl]) (by norm_num [numbersControl])
    · exact paired _ hD (by norm_num [numbersPuzzles]) (by norm_num [numbersPuzzles]) (by norm_num [numbersPuzzles])
  · have round_gain (x y : GroupSummary) {p q : GroupSummary} (hx : MatchesTable x p) (hy : MatchesTable y q)
        (d l u : ℝ) (delta : |q.gain-p.gain|+1/100 ≤ d) (lower : 0 < l)
        (l₁ : l ≤ p.gainSD-1/200) (l₂ : l ≤ q.gainSD-1/200)
        (u₁ : p.gainSD+1/200 ≤ u) (u₂ : q.gainSD+1/200 ≤ u)
        (ratio : 6*u ≤ 7*l) (small : 42*d^2 < 1.8^2*(2*l^2)) :
        0.05 < welchP (y.gain-x.gain) x.gainSD y.gainSD := by
      obtain ⟨al,au⟩ := abs_le.mp hx.gainSD
      obtain ⟨bl,bu⟩ := abs_le.mp hy.gainSD
      have hd := (abs_sub_abs_le_abs_sub (y.gain-x.gain) (q.gain-p.gain)).trans (difference_rounding hx.gain hy.gain)
      have hs₁ := pow_le_pow_left₀ lower.le (by linarith : l ≤ x.gainSD) 2
      have hs₂ := pow_le_pow_left₀ lower.le (by linarith : l ≤ y.gainSD) 2
      have hd₂ := pow_le_pow_left₀ (abs_nonneg (y.gain-x.gain)) (by linarith : |y.gain-x.gain|≤d) 2
      rw [sq_abs] at hd₂
      exact gain_welch (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨round_gain _ _ hA hB 0.06 3.57 3.63 (by norm_num [thinkingControl,thinkingPuzzles,abs_div]) (by norm_num)
      (by norm_num [thinkingControl]) (by norm_num [thinkingPuzzles]) (by norm_num [thinkingControl]) (by norm_num [thinkingPuzzles]) (by norm_num) (by norm_num),
      round_gain _ _ hC hD 0.54 19.49 21.09 (by norm_num [numbersControl,numbersPuzzles,abs_div]) (by norm_num)
      (by norm_num [numbersControl]) (by norm_num [numbersPuzzles]) (by norm_num [numbersControl]) (by norm_num [numbersPuzzles]) (by norm_num) (by norm_num)⟩

end Thesis.StudyANCOVA
