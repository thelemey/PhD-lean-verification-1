import Thesis.StudyANCOVA
import Mathlib.Data.Real.Sqrt

namespace Thesis.StudyANCOVA

/-- A value displayed to two decimal places in tab:descriptive. -/
def RoundsTo (actual printed : ℝ) : Prop := |actual - printed| ≤ 1 / 200

theorem difference_rounding {a b a' b' : ℝ} (ha : RoundsTo a a') (hb : RoundsTo b b') :
    |(b - a) - (b' - a')| ≤ 1 / 100 := by
  have h := abs_le.mp ha
  have h' := abs_le.mp hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Pool the centered sums for the two groups of 42. A sample standard
deviation contributes 41 times its square to the sum of squares. -/
noncomputable def withinSS (sA sB : ℝ) : ℝ := 41 * (sA ^ 2 + sB ^ 2)

/-- The sample standard deviation for the 42 pupils in a group. -/
noncomputable def sampleSD (x : Fin 42 → ℝ) : ℝ := Real.sqrt (ss x / 41)

private theorem ss_nonneg (x : Fin 42 → ℝ) : 0 ≤ ss x := by
  unfold ss
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem withinSS_sampleSD (xA xB : Fin 42 → ℝ) :
    withinSS (sampleSD xA) (sampleSD xB) = ss xA + ss xB := by
  unfold withinSS sampleSD
  rw [Real.sq_sqrt (div_nonneg (ss_nonneg xA) (by norm_num)),
    Real.sq_sqrt (div_nonneg (ss_nonneg xB) (by norm_num))]
  ring

/-- The paired standard deviations in tab:descriptive determine the pooled
cross product used by the common-slope fit. -/
theorem pooled_cross_of_sampleSD (xA yA xB yB : Fin 42 → ℝ) :
    let xx := withinSS (sampleSD xA) (sampleSD xB)
    let yy := withinSS (sampleSD yA) (sampleSD yB)
    let gg := withinSS (sampleSD (fun i => yA i - xA i)) (sampleSD (fun i => yB i - xB i))
    cross xA yA + cross xB yB = (xx + yy - gg) / 2 := by
  dsimp only
  rw [cross_eq_of_gain xA yA, cross_eq_of_gain xB yB]
  simp only [withinSS_sampleSD]
  ring

private theorem withinSS_bounds {a b sa sb : ℝ} (ha : 1 / 200 ≤ a) (hb : 1 / 200 ≤ b)
    (hA : RoundsTo sa a) (hB : RoundsTo sb b) :
    withinSS (a - 1 / 200) (b - 1 / 200) ≤ withinSS sa sb ∧
      withinSS sa sb ≤ withinSS (a + 1 / 200) (b + 1 / 200) := by
  obtain ⟨hAl, hAu⟩ := abs_le.mp hA
  obtain ⟨hBl, hBu⟩ := abs_le.mp hB
  have h₁ := pow_le_pow_left₀ (by linarith : 0 ≤ a - 1 / 200)
    (by linarith : a - 1 / 200 ≤ sa) 2
  have h₂ := pow_le_pow_left₀ (by linarith : 0 ≤ b - 1 / 200)
    (by linarith : b - 1 / 200 ≤ sb) 2
  have h₃ := pow_le_pow_left₀ (by linarith : 0 ≤ sa)
    (by linarith : sa ≤ a + 1 / 200) 2
  have h₄ := pow_le_pow_left₀ (by linarith : 0 ≤ sb)
    (by linarith : sb ≤ b + 1 / 200) 2
  unfold withinSS
  exact ⟨by linarith, by linarith⟩

noncomputable def adjustedDifference (dx dy xx xy : ℝ) : ℝ := dy - (xy / xx) * dx

noncomputable def residualVariance (xx yy xy : ℝ) : ℝ := (yy - xy ^ 2 / xx) / 81

/-- The square of the t statistic for the adjusted group contrast. -/
noncomputable def squaredT (dx dy xx yy xy : ℝ) : ℝ :=
  adjustedDifference dx dy xx xy ^ 2 /
    (residualVariance xx yy xy * (1 / 21 + dx ^ 2 / xx))

private theorem residualVariance_lower {xx yy xy minX minY maxXY v : ℝ}
    (hx : 0 < minX) (hxx : minX ≤ xx) (hyy : minY ≤ yy) (hxy : |xy| ≤ maxXY)
    (hv : v ≤ (minY - maxXY ^ 2 / minX) / 81) : v ≤ residualVariance xx yy xy := by
  have hz := pow_le_pow_left₀ (abs_nonneg xy) hxy 2
  rw [sq_abs] at hz
  have hfrac : xy ^ 2 / xx ≤ maxXY ^ 2 / minX :=
    (div_le_div_of_nonneg_left (sq_nonneg xy) hx hxx).trans
      (div_le_div_of_nonneg_right hz hx.le)
  unfold residualVariance
  linarith

private theorem squaredT_lt_of_bounds {dx dy xx yy xy maxG minV : ℝ}
    (hx : 0 < xx) (hv : 0 < minV) (hV : minV ≤ residualVariance xx yy xy)
    (hg : |adjustedDifference dx dy xx xy| ≤ maxG)
    (hcrit : maxG ^ 2 < (9 / 5 : ℝ) ^ 2 * (minV / 21)) :
    squaredT dx dy xx yy xy < (9 / 5 : ℝ) ^ 2 := by
  let factor : ℝ := 1 / 21 + dx ^ 2 / xx
  have hF : 1 / 21 ≤ factor := le_add_of_nonneg_right (div_nonneg (sq_nonneg dx) hx.le)
  have hf : 0 < factor := (by norm_num : (0 : ℝ) < 1 / 21).trans_le hF
  have hRV := hv.trans_le hV
  have hden : minV / 21 ≤ residualVariance xx yy xy * factor := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hV hF (by norm_num) hRV.le
  have hn := pow_le_pow_left₀ (abs_nonneg (adjustedDifference dx dy xx xy)) hg 2
  rw [sq_abs] at hn
  unfold squaredT
  apply (div_lt_iff₀ (mul_pos hRV hf)).2
  exact hn.trans_lt (hcrit.trans_le (mul_le_mul_of_nonneg_left hden (by norm_num)))

/-- Thinking test, tab:descriptive. The contrasts may vary by a cent
because each is the difference of two separately rounded means. -/
theorem thinking_ancova_enclosure {dx dy preA preB postA postB gainA gainB : ℝ}
    (hdx : |dx - 1.05| ≤ 1 / 100) (hdy : |dy - 1.00| ≤ 1 / 100)
    (hpreA : RoundsTo preA 2.30) (hpreB : RoundsTo preB 2.18)
    (hpostA : RoundsTo postA 2.87) (hpostB : RoundsTo postB 2.65)
    (hgainA : RoundsTo gainA 3.62) (hgainB : RoundsTo gainB 3.58) :
    let xx := withinSS preA preB
    let yy := withinSS postA postB
    let xy := (xx + yy - withinSS gainA gainB) / 2
    1 < adjustedDifference dx dy xx xy ∧ adjustedDifference dx dy xx xy < 1.06 ∧
      squaredT dx dy xx yy xy < (9 / 5 : ℝ) ^ 2 := by
  intro xx yy xy
  obtain ⟨hxl, hxu⟩ := withinSS_bounds (by norm_num) (by norm_num) hpreA hpreB
  obtain ⟨hyl, hyu⟩ := withinSS_bounds (by norm_num) (by norm_num) hpostA hpostB
  obtain ⟨hzl, hzu⟩ := withinSS_bounds (by norm_num) (by norm_num) hgainA hgainB
  change _ ≤ xx at hxl
  change xx ≤ _ at hxu
  change _ ≤ yy at hyl
  change yy ≤ _ at hyu
  norm_num [withinSS] at hxl hxu hyl hyu hzl hzu
  have hxy : -16.22 < xy ∧ xy < -9.16 := by
    dsimp only [xy, withinSS]
    exact ⟨by linarith, by linarith⟩
  have hx : 0 < xx := by linarith
  have hs₁ : -0.04 < xy / xx := (lt_div_iff₀ hx).2 (by linarith [hxy.1])
  have hs₂ : xy / xx < -0.02 := (div_lt_iff₀ hx).2 (by linarith [hxy.2])
  obtain ⟨hdxl, hdxu⟩ := abs_le.mp hdx
  obtain ⟨hdyl, hdyu⟩ := abs_le.mp hdy
  have hdx0 : 0 ≤ dx := by linarith
  have hmul₁ := mul_le_mul_of_nonneg_right hs₁.le hdx0
  have hmul₂ := mul_le_mul_of_nonneg_right hs₂.le hdx0
  have hg : 1 < adjustedDifference dx dy xx xy ∧ adjustedDifference dx dy xx xy < 1.06 := by
    unfold adjustedDifference
    exact ⟨by linarith, by linarith⟩
  refine ⟨hg.1, hg.2, squaredT_lt_of_bounds hx (maxG := 1.06) (minV := 7.6) (by norm_num) ?_ ?_ (by norm_num)⟩
  · apply residualVariance_lower (minX := 409) (minY := 623) (maxXY := 17) (by norm_num)
    · linarith
    · linarith
    · exact abs_le.mpr ⟨by linarith [hxy.1], by linarith [hxy.2]⟩
    · norm_num
  · rw [abs_of_pos (zero_lt_one.trans hg.1)]
    exact hg.2.le

/-- Numbers test, tab:descriptive, with the same rounding convention. -/
theorem numbers_ancova_enclosure {dx dy preA preB postA postB gainA gainB : ℝ}
    (hdx : |dx - 11.95| ≤ 1 / 100) (hdy : |dy - 12.47| ≤ 1 / 100)
    (hpreA : RoundsTo preA 24.68) (hpreB : RoundsTo preB 22.11)
    (hpostA : RoundsTo postA 21.61) (hpostB : RoundsTo postB 20.19)
    (hgainA : RoundsTo gainA 21.08) (hgainB : RoundsTo gainB 19.50) :
    let xx := withinSS preA preB
    let yy := withinSS postA postB
    let xy := (xx + yy - withinSS gainA gainB) / 2
    6.19 < adjustedDifference dx dy xx xy ∧ adjustedDifference dx dy xx xy < 6.26 ∧
      squaredT dx dy xx yy xy < (9 / 5 : ℝ) ^ 2 := by
  intro xx yy xy
  obtain ⟨hxl, hxu⟩ := withinSS_bounds (by norm_num) (by norm_num) hpreA hpreB
  obtain ⟨hyl, hyu⟩ := withinSS_bounds (by norm_num) (by norm_num) hpostA hpostB
  obtain ⟨hzl, hzu⟩ := withinSS_bounds (by norm_num) (by norm_num) hgainA hgainB
  change _ ≤ xx at hxl
  change xx ≤ _ at hxu
  change _ ≤ yy at hyl
  change yy ≤ _ at hyu
  norm_num [withinSS] at hxl hxu hyl hyu hzl hzu
  have hxy : 23506 < xy ∧ xy < 23560 := by
    dsimp only [xy, withinSS]
    exact ⟨by linarith, by linarith⟩
  have hx : 0 < xx := by linarith
  have hs₁ : 0.521 < xy / xx := (lt_div_iff₀ hx).2 (by linarith [hxy.1])
  have hs₂ : xy / xx < 0.524 := (div_lt_iff₀ hx).2 (by linarith [hxy.2])
  obtain ⟨hdxl, hdxu⟩ := abs_le.mp hdx
  obtain ⟨hdyl, hdyu⟩ := abs_le.mp hdy
  have hdx0 : 0 ≤ dx := by linarith
  have hmul₁ := mul_le_mul_of_nonneg_right hs₁.le hdx0
  have hmul₂ := mul_le_mul_of_nonneg_right hs₂.le hdx0
  have hg : 6.19 < adjustedDifference dx dy xx xy ∧ adjustedDifference dx dy xx xy < 6.26 := by
    unfold adjustedDifference
    exact ⟨by linarith, by linarith⟩
  refine ⟨hg.1, hg.2, squaredT_lt_of_bounds hx (maxG := 6.26) (minV := 290) (by norm_num) ?_ ?_ (by norm_num)⟩
  · apply residualVariance_lower (minX := 44996) (minY := 35842) (maxXY := 23560) (by norm_num)
    · linarith
    · linarith
    · exact abs_le.mpr ⟨by linarith [hxy.1], hxy.2.le⟩
    · norm_num
  · rw [abs_of_pos ((by norm_num : (0 : ℝ) < 6.19).trans hg.1)]
    exact hg.2.le

/-- For equal group sizes, the squared Welch statistic from the printed
mean contrast and within-group sum of squares. -/
noncomputable def welchSquared (difference pooledSS : ℝ) : ℝ :=
  difference ^ 2 / (pooledSS / (41 * 42))

private theorem welch_lower {d S lo hi t : ℝ} (hlo : 0 ≤ lo) (hd : lo ≤ d)
    (hS : 0 < S) (hhi : S ≤ hi) (hcrit : t ^ 2 * (hi / (41 * 42)) < lo ^ 2) :
    t ^ 2 < welchSquared d S := by
  apply (lt_div_iff₀ (div_pos hS (by norm_num))).2
  exact ((mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hhi (by norm_num))
    (sq_nonneg t)).trans_lt hcrit).trans_le (pow_le_pow_left₀ hlo hd 2)

private theorem welch_upper {d S hi lo t : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ hi)
    (hlo : 0 < lo) (hS : lo ≤ S) (hcrit : hi ^ 2 < t ^ 2 * (lo / (41 * 42))) :
    welchSquared d S < t ^ 2 := by
  apply (div_lt_iff₀ (div_pos (hlo.trans_le hS) (by norm_num))).2
  exact ((pow_le_pow_left₀ hd0 hd 2).trans_lt hcrit).trans_le
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hS (by norm_num)) (sq_nonneg t))

/-- The thinking instrument has a clear pre-test contrast and a smaller
unadjusted post-test statistic, across the table's rounding intervals. -/
theorem thinking_welch_enclosure {dx dy preA preB postA postB : ℝ}
    (hdx : |dx - 1.05| ≤ 1 / 100) (hdy : |dy - 1.00| ≤ 1 / 100)
    (hpreA : RoundsTo preA 2.30) (hpreB : RoundsTo preB 2.18)
    (hpostA : RoundsTo postA 2.87) (hpostB : RoundsTo postB 2.65) :
    (2.1 : ℝ) ^ 2 < welchSquared dx (withinSS preA preB) ∧
      welchSquared dy (withinSS postA postB) < (1.8 : ℝ) ^ 2 := by
  obtain ⟨hxlo, hxhi⟩ := withinSS_bounds (by norm_num) (by norm_num) hpreA hpreB
  obtain ⟨hylo, _⟩ := withinSS_bounds (by norm_num) (by norm_num) hpostA hpostB
  obtain ⟨hdxl, _⟩ := abs_le.mp hdx
  obtain ⟨hdyl, hdyu⟩ := abs_le.mp hdy
  constructor
  · apply welch_lower (lo := 1.04) (hi := 414) (by norm_num) (by linarith)
    · exact (by norm_num [withinSS] : 0 < withinSS (2.30 - 1 / 200) (2.18 - 1 / 200)).trans_le hxlo
    · exact hxhi.trans (by norm_num [withinSS])
    · norm_num
  · exact welch_upper (by linarith) (hi := 1.01) (by linarith) (lo := 623)
      (by norm_num) ((by norm_num [withinSS] : 623 ≤ withinSS (2.87 - 1 / 200) (2.65 - 1 / 200)).trans hylo) (by norm_num)

/-- The numbers instrument shows large unadjusted contrasts both before
and after instruction, uniformly over the printed rounding intervals. -/
theorem numbers_welch_enclosure {dx dy preA preB postA postB : ℝ}
    (hdx : |dx - 11.95| ≤ 1 / 100) (hdy : |dy - 12.47| ≤ 1 / 100)
    (hpreA : RoundsTo preA 24.68) (hpreB : RoundsTo preB 22.11)
    (hpostA : RoundsTo postA 21.61) (hpostB : RoundsTo postB 20.19) :
    (2.1 : ℝ) ^ 2 < welchSquared dx (withinSS preA preB) ∧
      (2.5 : ℝ) ^ 2 < welchSquared dy (withinSS postA postB) := by
  obtain ⟨hxlo, hxhi⟩ := withinSS_bounds (by norm_num) (by norm_num) hpreA hpreB
  obtain ⟨hylo, hyhi⟩ := withinSS_bounds (by norm_num) (by norm_num) hpostA hpostB
  obtain ⟨hdxl, _⟩ := abs_le.mp hdx
  obtain ⟨hdyl, _⟩ := abs_le.mp hdy
  constructor
  · apply welch_lower (lo := 11.94) (hi := 45036) (by norm_num) (by linarith)
    · exact (by norm_num [withinSS] : 0 < withinSS (24.68 - 1 / 200) (22.11 - 1 / 200)).trans_le hxlo
    · exact hxhi.trans (by norm_num [withinSS])
    · norm_num
  · apply welch_lower (lo := 12.46) (hi := 35877) (by norm_num) (by linarith)
    · exact (by norm_num [withinSS] : 0 < withinSS (21.61 - 1 / 200) (20.19 - 1 / 200)).trans_le hylo
    · exact hyhi.trans (by norm_num [withinSS])
    · norm_num

end Thesis.StudyANCOVA
