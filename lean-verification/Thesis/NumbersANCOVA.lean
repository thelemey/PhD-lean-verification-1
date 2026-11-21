import Thesis.StudyCriticalValues
import Thesis.StudyRoundingBounds

open Real Set

namespace Thesis.StudyANCOVA

theorem PairedGroup.summary_gain (g : PairedGroup) : g.summary.gain = g.summary.post-g.summary.pre :=
  mean_sub g.pre g.post

/-- The paired change is an additional printed mean. Its identity with
post minus pre narrows the admissible *unrounded* group means. -/
theorem numbers_mean_contrasts (A B : GroupSummary) (hA : MatchesTable A numbersControl)
    (hB : MatchesTable B numbersPuzzles) (ga : A.gain = A.post-A.pre) (gb : B.gain = B.post-B.pre) :
    Bounds (B.pre-A.pre) 11.940 11.955 ∧ Bounds (B.post-A.post) 12.465 12.480 ∧
    Bounds (B.gain-A.gain) 0.520 0.540 ∧
    Bounds ((B.post-A.post)-0.523*(B.pre-A.pre)) 6.217765 6.232765 := by
  obtain ⟨px,py⟩ := abs_le.mp hA.pre
  obtain ⟨qx,qy⟩ := abs_le.mp hB.pre
  obtain ⟨sx,sy⟩ := abs_le.mp hA.post
  obtain ⟨tx,ty⟩ := abs_le.mp hB.post
  obtain ⟨gx,gy⟩ := abs_le.mp hA.gain
  obtain ⟨hx,hy⟩ := abs_le.mp hB.gain
  dsimp only [numbersControl,numbersPuzzles] at px py qx qy sx sy tx ty gx gy hx hy
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    simp only [Rat.cast_ofScientific] <;> linarith

/-- The rounded standard deviations bound each within-group sum of squares. -/
theorem pooled_bounds {sa sb : ℝ} (a b : ℚ) (ha : RoundsTo sa (a:ℝ)) (hb : RoundsTo sb (b:ℝ))
    (la : 0 ≤ a-1/200) (lb : 0 ≤ b-1/200) :
    Bounds (withinSS sa sb) (41*((a-1/200)^2+(b-1/200)^2)) (41*((a+1/200)^2+(b+1/200)^2)) := by
  have h := (((Bounds.of_rounding a ha).sq la).add ((Bounds.of_rounding b hb).sq lb)).scale 41 (by decide +kernel)
  simpa only [withinSS,Rat.cast_ofNat] using h

noncomputable def pooledSlope (a b : GroupSummary) : ℝ :=
  let xx := withinSS a.preSD b.preSD
  ((xx+withinSS a.postSD b.postSD-withinSS a.gainSD b.gainSD)/2)/xx

noncomputable def ancovaResidualVariance (a b : GroupSummary) : ℝ :=
  let xx := withinSS a.preSD b.preSD
  let yy := withinSS a.postSD b.postSD
  residualVariance xx yy ((xx+yy-withinSS a.gainSD b.gainSD)/2)

/-- Common-slope, residual-variance and adjusted-contrast enclosures from
Table 4.3 alone. Centering the algebra at 0.523 avoids counting the same
uncertain sum of squares twice in the residual error. -/
theorem numbers_adjustment_from_summaries (A B : GroupSummary) (hA : MatchesTable A numbersControl)
    (hB : MatchesTable B numbersPuzzles) (ga : A.gain = A.post-A.pre) (gb : B.gain = B.post-B.pre) :
    Bounds (pooledSlope A B) 0.52239 0.523161 ∧
    Bounds (ancovaResidualVariance A B) 290.56 291.10 ∧
    Bounds (ancovaContrast A B) 6.2158 6.2401 ∧
    Bounds (sqrt (ancovaStandardErrorSq A B)) 3.8413 3.8454 := by
  let X := withinSS A.preSD B.preSD
  let Y := withinSS A.postSD B.postSD
  let G := withinSS A.gainSD B.gainSD
  let C := (X+Y-G)/2
  let β := C/X
  let dx := B.pre-A.pre
  let dy := B.post-A.post
  have xx : Bounds X 44996.9526 45035.3205 := (pooled_bounds 24.68 22.11 hA.preSD hB.preSD
    (by decide +kernel) (by decide +kernel)).widen (by decide +kernel) (by decide +kernel)
  have yy : Bounds Y 35842.6202 35876.8963 := (pooled_bounds 21.61 20.19 hA.postSD hB.postSD
    (by decide +kernel) (by decide +kernel)).widen (by decide +kernel) (by decide +kernel)
  have gg : Bounds G 33792.6366 33825.9123 := (pooled_bounds 21.08 19.50 hA.gainSD hB.gainSD
    (by decide +kernel) (by decide +kernel)).widen (by decide +kernel) (by decide +kernel)
  obtain ⟨dd,_,_,dc⟩ := numbers_mean_contrasts A B hA hB ga gb
  have xp : 0 < X := (by norm_num : (0:ℝ) < (44996.9526:ℚ)).trans_le xx.lower
  have bform : β = (1/2:ℝ)*(1+(Y-G)/X) := by dsimp [β,C]; field_simp; ring
  have beta : Bounds β 0.52239 0.523161 := by
    rw [bform]
    have h := ((Bounds.exactValue 1).add ((yy.sub gg).div xx (by decide +kernel) (by decide +kernel))).scale (1/2) (by decide +kernel)
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h.widen
      (l := 0.52239) (u := 0.523161) (by decide +kernel) (by decide +kernel)
  have bs := beta.sub (Bounds.exactValue 0.523)
  have ebd : |β-0.523| ≤ 0.00061 := by
    obtain ⟨hl,hu⟩ := bs
    norm_num at hl hu
    exact abs_le.2 ⟨by linarith,by linarith⟩
  have esq : Bounds ((β-0.523)^2) 0 (0.00061^2) := by
    refine ⟨by simpa using sq_nonneg (β-0.523),?_⟩
    simpa only [Rat.cast_pow,Rat.cast_ofScientific,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ebd 2
  have resId : ancovaResidualVariance A B =
      (1/81:ℝ)*((0.477*Y+0.523*G)-(0.523*0.477)*X-(β-0.523)^2*X) := by
    change (Y-C^2/X)/81 = _
    dsimp only [β,C]
    field_simp
    ring
  have var : Bounds (ancovaResidualVariance A B) 290.56 291.10 := by
    rw [resId]
    have h := (((((yy.scale 0.477 (by decide +kernel)).add (gg.scale 0.523 (by decide +kernel))).sub
      (xx.scale (0.523*0.477) (by decide +kernel))).sub (esq.mul xx (by decide +kernel) (by decide +kernel))).scale (1/81) (by decide +kernel))
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_ofScientific] using
      h.widen (l := 290.56) (u := 291.10) (by decide +kernel) (by decide +kernel)
  have ctr : Bounds (ancovaContrast A B) 6.2158 6.2401 := by
    change Bounds (dy-β*dx) _ _
    change Bounds (dy-0.523*dx) _ _ at dc
    change Bounds dx _ _ at dd
    obtain ⟨bl,bu⟩ := beta
    obtain ⟨dl,du⟩ := dd
    obtain ⟨cl,cu⟩ := dc
    simp only [Rat.cast_ofScientific] at bl bu dl du cl cu
    have dl' : 0 ≤ dx := (by norm_num : (0:ℝ) ≤ 11.940).trans dl
    have m₁ := mul_le_mul_of_nonneg_right (by linarith only [bl] : -0.00061 ≤ β-0.523) dl'
    have m₂ := mul_le_mul_of_nonneg_right (by linarith only [bu] : β-0.523 ≤ 0.000161) dl'
    constructor <;> simp only [Rat.cast_ofScientific] <;> linarith only [du,cl,cu,m₁,m₂]
  have se : Bounds (sqrt (ancovaStandardErrorSq A B)) 3.8413 3.8454 := by
    change Bounds (sqrt (ancovaResidualVariance A B*(1/21+dx^2/X))) _ _
    have f := (Bounds.exactValue (1/21)).add ((dd.sq (by decide +kernel)).div xx (by decide +kernel) (by decide +kernel))
    have h := (var.mul f (by decide +kernel) (by decide +kernel)).sqrt 3.8413 3.8454 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  exact ⟨beta,var,ctr,se⟩


theorem sqrt_ancovaSquaredT {A B : GroupSummary} (hg : 0 ≤ ancovaContrast A B)
    (hs : 0 < sqrt (ancovaStandardErrorSq A B)) :
    sqrt (ancovaSquaredT A B) = ancovaContrast A B/sqrt (ancovaStandardErrorSq A B) := by
  have hv := (sqrt_pos.1 hs).le
  change sqrt ((ancovaContrast A B)^2/ancovaStandardErrorSq A B) = _
  rw [sqrt_div (sq_nonneg _),sqrt_sq hg]

/-- The numerical conclusion for the hundred-point instrument, independent
of the printed ANCOVA row. Only the twelve descriptive means and standard
deviations (including paired gains) are read from the dissertation. -/
theorem numbers_ancova_from_paired_scores (A B : PairedGroup)
    (hA : MatchesTable A.summary numbersControl) (hB : MatchesTable B.summary numbersPuzzles) :
    let a := A.summary
    let b := B.summary
    let g := ancovaContrast a b
    let se := sqrt (ancovaStandardErrorSq a b)
    let t := sqrt (ancovaSquaredT a b)
    Bounds (ancovaP a b) 0.1081 0.10995 ∧ Bounds t 1.6164 1.6245 ∧
    Bounds (g-critical95*se) (-1.441) (-1.400) ∧ Bounds (g+critical95*se) 13.856 13.897 ∧
    Bounds (g/sqrt (ancovaResidualVariance a b)) 0.3643 0.3661 ∧
    Bounds (t^2/(81+t^2)) 0.0312 0.0316 := by
  intro a b g se t
  obtain ⟨_,var,ctr,ser⟩ := numbers_adjustment_from_summaries a b hA hB A.summary_gain B.summary_gain
  have hg : 0 ≤ g := (by norm_num : 0 ≤ ((6.2158:ℚ):ℝ)).trans ctr.lower
  have hs : 0 < se := (by norm_num : 0 < ((3.8413:ℚ):ℝ)).trans_le ser.lower
  have te : t = g/se := sqrt_ancovaSquaredT hg hs
  have tt : Bounds t 1.6164 1.6245 := te ▸ (ctr.div ser (by decide +kernel) (by decide +kernel)).widen
    (by decide +kernel) (by decide +kernel)
  have p₁ := (reference81 1.6245 0.1081 0.1082 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).1
  have p₂ := (reference81 1.6164 0.10985 0.10995 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2
  have monot := (studentProbability_strictAnti (v:=81) (by norm_num)).antitoneOn
  have pl := p₁.trans (monot (sqrt_nonneg _) (by norm_num) tt.upper)
  have pu := (monot (by norm_num) (sqrt_nonneg _) tt.lower).trans p₂
  have crit : Bounds critical95 1.989 1.991 := ⟨critical95_bounds.1,critical95_bounds.2⟩
  have width := crit.mul ser (by decide +kernel) (by decide +kernel)
  have sd := var.sqrt 17.0458 17.0617 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have sqt := tt.sq (by decide +kernel)
  have den := (Bounds.exactValue 81).add sqt
  have eta := sqt.div den (by decide +kernel) (by decide +kernel)
  refine ⟨⟨pl,pu⟩,tt,(ctr.sub width).widen (by decide +kernel) (by decide +kernel),
    (ctr.add width).widen (by decide +kernel) (by decide +kernel),
    (ctr.div sd (by decide +kernel) (by decide +kernel)).widen (by decide +kernel) (by decide +kernel),?_⟩
  simpa only [Rat.cast_ofNat] using eta.widen (l:=0.0312) (u:=0.0316) (by decide +kernel) (by decide +kernel)

/-- The adjusted means at the pooled baseline correspond to the displayed
confidence limits. Both point estimates leave room for a positive effect;
both 95% intervals include zero. -/
theorem numbers_adjusted_means (A B : PairedGroup)
    (hA : MatchesTable A.summary numbersControl) (hB : MatchesTable B.summary numbersPuzzles) :
    let a := A.summary
    let b := B.summary
    let g := ancovaContrast a b
    Bounds ((a.post+b.post-g)/2) 68.469 68.493 ∧
      Bounds ((a.post+b.post+g)/2) 74.697 74.721 := by
  obtain ⟨_,_,ctr,_⟩ := numbers_adjustment_from_summaries A.summary B.summary hA hB A.summary_gain B.summary_gain
  obtain ⟨gl,gu⟩ := ctr
  obtain ⟨al,au⟩ := abs_le.mp hA.post
  obtain ⟨bl,bu⟩ := abs_le.mp hB.post
  dsimp only [numbersControl,numbersPuzzles] at al au bl bu
  simp only [Rat.cast_ofScientific] at gl gu
  dsimp only
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> simp only [Rat.cast_ofScientific] <;> linarith only [gl,gu,al,au,bl,bu]

end Thesis.StudyANCOVA
