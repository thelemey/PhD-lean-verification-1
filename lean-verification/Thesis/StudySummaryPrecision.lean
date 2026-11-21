import Thesis.NumbersANCOVA

open Real

namespace Thesis.StudyANCOVA

/-! Logical precision of the published descriptive table. The finite inputs
below witness non-uniqueness of the rounded ANCOVA output. They are
mathematical examples, never estimates of the pupils' missing scores. -/

private abbrev Column := Fin 42 → ℚ
private def average (x : Column) : ℚ := (∑ i, x i)/42
private def centeredSS (x : Column) : ℚ := ∑ i, (x i-average x)^2
private def realColumn (x : Column) (i : Fin 42) : ℝ := x i

private theorem mean_realColumn (x : Column) : mean (realColumn x) = (average x:ℝ) := by
  simp [mean,realColumn,average]

private theorem ss_realColumn (x : Column) : ss (realColumn x) = (centeredSS x:ℝ) := by
  simp [ss,centered,mean_realColumn,centeredSS,realColumn]

private structure Pair where
  pre : Column
  post : Column

private def Pair.real (g : Pair) : PairedGroup := ⟨realColumn g.pre,realColumn g.post⟩
private def Pair.change (g : Pair) : Column := fun i => g.post i-g.pre i

private theorem real_change (g : Pair) :
    (fun i => g.real.post i-g.real.pre i) = realColumn g.change := by
  funext i
  simp [Pair.real,realColumn,Pair.change]

private def certifiedColumn (x : Column) (m s : ℚ) : Prop :=
  m-1/200 ≤ average x ∧ average x ≤ m+1/200 ∧ 0 ≤ s-1/200 ∧
  (s-1/200)^2 ≤ centeredSS x/41 ∧ centeredSS x/41 ≤ (s+1/200)^2

private instance (x : Column) (m s : ℚ) : Decidable (certifiedColumn x m s) := by
  unfold certifiedColumn
  infer_instance

private theorem certifiedColumn_matches {x : Column} {m s : ℚ} (h : certifiedColumn x m s) :
    RoundsTo (mean (realColumn x)) (m:ℝ) ∧ RoundsTo (sampleSD (realColumn x)) (s:ℝ) := by
  obtain ⟨ml,mu,sp,sl,su⟩ := h
  have ave : Bounds (mean (realColumn x)) (m-1/200) (m+1/200) := by
    rw [mean_realColumn]
    exact ⟨by exact_mod_cast ml,by exact_mod_cast mu⟩
  have sq : Bounds (ss (realColumn x)/41) ((s-1/200)^2) ((s+1/200)^2) := by
    rw [ss_realColumn]
    exact ⟨by exact_mod_cast sl,by exact_mod_cast su⟩
  have sd := sq.sqrt (s-1/200) (s+1/200) le_rfl le_rfl (by linarith)
  exact ⟨ave.rounds _ le_rfl le_rfl,sd.rounds _ le_rfl le_rfl⟩

/-- Two 21-element blocks and a balanced contrast within each block give
bounded, explicitly paired rational inputs. -/
private def pairOf (m p s k l : ℚ) : Pair :=
  let z (i : Fin 42) : ℚ := if i.val < 21 then 1 else -1
  let w (i : Fin 42) : ℚ := if i.val%21 < 10 then 1 else if i.val%21 < 20 then -1 else 0
  ⟨fun i => m+k*z i+l*w i,fun i => p+s*z i⟩

private def control₁ := pairOf 47.79 65.3555 21.347 14.441 20.139
private def puzzles₁ := pairOf 59.7355 77.8345 19.944 12.631 18.268
private def control₂ := pairOf 47.79 65.3645 21.355 14.442 20.128
private def puzzles₂ := pairOf 59.7355 77.831 19.952 12.632 18.258

private theorem control_matches (g : Pair) (h : certifiedColumn g.pre 47.79 24.68 ∧
    certifiedColumn g.post 65.36 21.61 ∧ certifiedColumn g.change 17.57 21.08) :
    MatchesTable g.real.summary numbersControl := by
  obtain ⟨px,ps⟩ := certifiedColumn_matches h.1
  obtain ⟨yx,ys⟩ := certifiedColumn_matches h.2.1
  obtain ⟨gx,gs⟩ := certifiedColumn_matches h.2.2
  refine ⟨px,yx,?_,ps,ys,?_⟩ <;> dsimp only [PairedGroup.summary] <;> rw [real_change]
  · exact gx
  · exact gs

private theorem puzzles_matches (g : Pair) (h : certifiedColumn g.pre 59.74 22.11 ∧
    certifiedColumn g.post 77.83 20.19 ∧ certifiedColumn g.change 18.10 19.50) :
    MatchesTable g.real.summary numbersPuzzles := by
  obtain ⟨px,ps⟩ := certifiedColumn_matches h.1
  obtain ⟨yx,ys⟩ := certifiedColumn_matches h.2.1
  obtain ⟨gx,gs⟩ := certifiedColumn_matches h.2.2
  refine ⟨px,yx,?_,ps,ys,?_⟩ <;> dsimp only [PairedGroup.summary] <;> rw [real_change]
  · exact gx
  · exact gs

private def squaredStatistic (a b : Pair) : ℚ :=
  let X := centeredSS a.pre + centeredSS b.pre
  let Y := centeredSS a.post + centeredSS b.post
  let S := centeredSS a.change + centeredSS b.change
  let C := (X+Y-S)/2
  let dx := average b.pre-average a.pre
  let dy := average b.post-average a.post
  (dy-C/X*dx)^2 / (((Y-C^2/X)/81)*(1/21+dx^2/X))

private theorem squaredStatistic_eq (a b : Pair) :
    ancovaSquaredT a.real.summary b.real.summary = (squaredStatistic a b : ℝ) := by
  unfold squaredStatistic ancovaSquaredT squaredT adjustedDifference residualVariance
  dsimp only [PairedGroup.summary]
  rw [real_change,real_change]
  simp only [Pair.real,mean_realColumn,withinSS_sampleSD,ss_realColumn]
  push_cast
  rfl

/-- Scores in both columns respect the published 0–100 scale. -/
def InNumbersScale (g : PairedGroup) : Prop :=
  ∀ i, (0 ≤ g.pre i ∧ g.pre i ≤ 100) ∧ (0 ≤ g.post i ∧ g.post i ≤ 100)

private theorem checkedScale (g : Pair)
    (h : ∀ i, (0 ≤ g.pre i ∧ g.pre i ≤ 100) ∧ (0 ≤ g.post i ∧ g.post i ≤ 100)) :
    InNumbersScale g.real := by
  intro i
  dsimp only [Pair.real,realColumn]
  exact_mod_cast h i

private theorem probability_bounds (a b : Pair) (lo hi : ℚ) (low high : ℝ)
    (pos : 0 ≤ lo) (pos' : 0 ≤ hi)
    (hl : lo^2 ≤ squaredStatistic a b) (hu : squaredStatistic a b ≤ hi^2)
    (pl : low ≤ studentTwoSidedP 81 (hi:ℝ)) (pu : studentTwoSidedP 81 (lo:ℝ) ≤ high) :
    low ≤ ancovaP a.real.summary b.real.summary ∧ ancovaP a.real.summary b.real.summary ≤ high := by
  rw [ancovaP,squaredStatistic_eq]
  have l : (lo:ℝ) ≤ sqrt (squaredStatistic a b : ℝ) := le_sqrt_of_sq_le (by exact_mod_cast hl)
  have u : sqrt (squaredStatistic a b : ℝ) ≤ (hi:ℝ) := sqrt_le_iff.2 ⟨by exact_mod_cast pos',by exact_mod_cast hu⟩
  have mono := (studentProbability_strictAnti (v:=81) (by norm_num)).antitoneOn
  exact ⟨pl.trans (mono (sqrt_nonneg _) (show 0 ≤ (hi:ℝ) by exact_mod_cast pos') u),
    (mono (show 0 ≤ (lo:ℝ) by exact_mod_cast pos) (sqrt_nonneg _) l).trans pu⟩

set_option maxHeartbeats 1200000 in
/-- The descriptive table alone does not fix the third decimal of the
hundred-point adjusted p value. In each case all twelve rounded entries
match and all 84 pairs lie on the stated scoring scale. -/
theorem numbers_ancova_third_decimal_not_determined :
    let possible := fun (l u : ℝ) => ∃ a b : PairedGroup, InNumbersScale a ∧ InNumbersScale b ∧
      MatchesTable a.summary numbersControl ∧ MatchesTable b.summary numbersPuzzles ∧
      l < ancovaP a.summary b.summary ∧ ancovaP a.summary b.summary < u
    possible 0.1075 0.1085 ∧ possible 0.1095 0.1105 := by
  have p₁ := reference81 1.62322 0.10839 0.10848 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have p₂ := reference81 1.62320 0.10839 0.10848 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have p₃ := reference81 1.61782 0.10955 0.10964 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have p₄ := reference81 1.61780 0.10955 0.10964 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have ⟨ll,lu⟩ := probability_bounds control₁ puzzles₁ 1.62320 1.62322 _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) p₁.1 p₂.2
  have ⟨hl,hu⟩ := probability_bounds control₂ puzzles₂ 1.61780 1.61782 _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) p₃.1 p₄.2
  simp only [Rat.cast_ofScientific] at ll lu hl hu
  exact ⟨⟨_,_,checkedScale control₁ (by decide +kernel),checkedScale puzzles₁ (by decide +kernel),
    control_matches _ (by decide +kernel),puzzles_matches _ (by decide +kernel),
    by linarith only [ll],by linarith only [lu]⟩,
    ⟨_,_,checkedScale control₂ (by decide +kernel),checkedScale puzzles₂ (by decide +kernel),
    control_matches _ (by decide +kernel),puzzles_matches _ (by decide +kernel),
    by linarith only [hl],by linarith only [hu]⟩⟩

end Thesis.StudyANCOVA
