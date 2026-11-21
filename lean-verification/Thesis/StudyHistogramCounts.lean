import Thesis.StudyHistogram

open Finset

namespace Thesis.StudyANCOVA

/-- Integer bar heights, in pixels, at the 11 bin centers of fig11.pdf.
The baselines are rows 79 and 143 of its 438 × 429 embedded image. -/
def figure11ControlHeights : Fin 11 → ℕ := ![3,3,3,3,3,10,23,33,36,13,7]
def figure11PuzzleHeights : Fin 11 → ℕ := ![0,7,0,0,0,4,14,23,30,39,23]

/-- A common vertical scale in a panel, allowing a full pixel of raster
uncertainty in each bar and using the reported class size. -/
structure FitsBars (pixels counts : Fin 11 → ℕ) (scale : ℝ) : Prop where
  total : ∑ i, counts i = 42
  raster : ∀ i, |(pixels i:ℝ)-scale*(counts i:ℝ)| ≤ 1

private theorem bar_constraints {pixels counts : Fin 11 → ℕ} {scale : ℝ} (h : FitsBars pixels counts scale)
    (H : ℕ) (hs : ∑ i, pixels i = H) (H₀ : 11 ≤ H) :
    (∀ i, 42*pixels i ≤ (H+11)*counts i+42 ∧ (H-11)*counts i ≤ 42*(pixels i+1)) ∧
    ∀ i j, counts i*pixels j ≤ counts j*(pixels i+1)+counts i := by
  have lower (i) := (abs_le.mp (h.raster i)).1
  have upper (i) := (abs_le.mp (h.raster i)).2
  have hl := sum_le_sum (s:=univ) (fun i _ => lower i)
  have hu := sum_le_sum (s:=univ) (fun i _ => upper i)
  have nh : (∑ i, (pixels i:ℝ)) = H := by exact_mod_cast hs
  have nc : (∑ i, (counts i:ℝ)) = 42 := by exact_mod_cast h.total
  simp only [sum_sub_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,nh,nc] at hl hu
  norm_num at hl hu
  constructor
  · intro i
    have ml := mul_le_mul_of_nonneg_right (show (H:ℝ)-11 ≤ scale*42 by linarith only [hu])
      (Nat.cast_nonneg (counts i) (α:=ℝ))
    have mu := mul_le_mul_of_nonneg_right (show scale*42 ≤ (H:ℝ)+11 by linarith only [hl])
      (Nat.cast_nonneg (counts i) (α:=ℝ))
    constructor
    · exact_mod_cast (show (42:ℝ)*pixels i ≤ ((H:ℝ)+11)*counts i+42 by linarith only [mu,upper i])
    · have Hsub : ((H-11:ℕ):ℝ) = (H:ℝ)-11 := by rw [Nat.cast_sub H₀]; norm_num
      exact_mod_cast (show ((H-11:ℕ):ℝ)*counts i ≤ 42*((pixels i:ℝ)+1) by rw [Hsub]; linarith only [ml,lower i])
  · intro i j
    have l := mul_le_mul_of_nonneg_left (show (pixels j:ℝ) ≤ scale*counts j+1 by linarith only [upper j])
      (Nat.cast_nonneg (counts i) (α:=ℝ))
    have u := mul_le_mul_of_nonneg_left (show scale*counts i ≤ (pixels i:ℝ)+1 by linarith only [lower i])
      (Nat.cast_nonneg (counts j) (α:=ℝ))
    exact_mod_cast (show (counts i:ℝ)*pixels j ≤ counts j*((pixels i:ℝ)+1)+counts i by linarith only [l,u])

private theorem control_counts {f : Fin 11 → ℕ} {scale : ℝ} (h : FitsBars figure11ControlHeights f scale) : f = figure11Control := by
  obtain ⟨point,cross⟩ := bar_constraints h 137 (by decide +kernel) (by decide)
  have mixed : f 7 * 36 ≤ f 8 * 34 + f 7 := cross 7 8
  have total : f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7+f 8+f 9+f 10 = 42 := by simpa [Fin.sum_univ_succ,add_assoc] using h.total
  have b0 : 126 ≤ 148 * f 0 + 42 ∧ 126 * f 0 ≤ 168 := point 0
  have b1 : 126 ≤ 148 * f 1 + 42 ∧ 126 * f 1 ≤ 168 := point 1
  have b2 : 126 ≤ 148 * f 2 + 42 ∧ 126 * f 2 ≤ 168 := point 2
  have b3 : 126 ≤ 148 * f 3 + 42 ∧ 126 * f 3 ≤ 168 := point 3
  have b4 : 126 ≤ 148 * f 4 + 42 ∧ 126 * f 4 ≤ 168 := point 4
  have b5 : 420 ≤ 148 * f 5 + 42 ∧ 126 * f 5 ≤ 462 := point 5
  have b6 : 966 ≤ 148 * f 6 + 42 ∧ 126 * f 6 ≤ 1008 := point 6
  have b7 : 1386 ≤ 148 * f 7 + 42 ∧ 126 * f 7 ≤ 1428 := point 7
  have b8 : 1512 ≤ 148 * f 8 + 42 ∧ 126 * f 8 ≤ 1554 := point 8
  have b9 : 546 ≤ 148 * f 9 + 42 ∧ 126 * f 9 ≤ 588 := point 9
  have b10 : 294 ≤ 148 * f 10 + 42 ∧ 126 * f 10 ≤ 336 := point 10
  have hs : f 0 = 1 ∧ f 1 = 1 ∧ f 2 = 1 ∧ f 3 = 1 ∧ f 4 = 1 ∧ f 5 = 3 ∧ f 6 = 7 ∧ f 7 = 10 ∧ f 8 = 11 ∧ f 9 = 4 ∧ f 10 = 2 := by omega
  obtain ⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10⟩ := hs
  funext i
  fin_cases i <;> assumption

private theorem puzzles_counts {f : Fin 11 → ℕ} {scale : ℝ} (h : FitsBars figure11PuzzleHeights f scale) : f = figure11Puzzles := by
  obtain ⟨point,cross⟩ := bar_constraints h 140 (by decide +kernel) (by decide)
  have mixed : f 8 * 39 ≤ f 9 * 31 + f 8 := cross 8 9
  have total : f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7+f 8+f 9+f 10 = 42 := by simpa [Fin.sum_univ_succ,add_assoc] using h.total
  have b0 : 0 ≤ 151 * f 0 + 42 ∧ 129 * f 0 ≤ 42 := point 0
  have b1 : 294 ≤ 151 * f 1 + 42 ∧ 129 * f 1 ≤ 336 := point 1
  have b2 : 0 ≤ 151 * f 2 + 42 ∧ 129 * f 2 ≤ 42 := point 2
  have b3 : 0 ≤ 151 * f 3 + 42 ∧ 129 * f 3 ≤ 42 := point 3
  have b4 : 0 ≤ 151 * f 4 + 42 ∧ 129 * f 4 ≤ 42 := point 4
  have b5 : 168 ≤ 151 * f 5 + 42 ∧ 129 * f 5 ≤ 210 := point 5
  have b6 : 588 ≤ 151 * f 6 + 42 ∧ 129 * f 6 ≤ 630 := point 6
  have b7 : 966 ≤ 151 * f 7 + 42 ∧ 129 * f 7 ≤ 1008 := point 7
  have b8 : 1260 ≤ 151 * f 8 + 42 ∧ 129 * f 8 ≤ 1302 := point 8
  have b9 : 1638 ≤ 151 * f 9 + 42 ∧ 129 * f 9 ≤ 1680 := point 9
  have b10 : 966 ≤ 151 * f 10 + 42 ∧ 129 * f 10 ≤ 1008 := point 10
  have hs : f 0 = 0 ∧ f 1 = 2 ∧ f 2 = 0 ∧ f 3 = 0 ∧ f 4 = 0 ∧ f 5 = 1 ∧ f 6 = 4 ∧ f 7 = 7 ∧ f 8 = 9 ∧ f 9 = 12 ∧ f 10 = 7 := by omega
  obtain ⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10⟩ := hs
  funext i
  fin_cases i <;> assumption

/-- The frequencies in both panels are uniquely determined within the
stated raster tolerance. The given calibration is feasible in both cases. -/
theorem figure11_raster_counts :
    (∃ scale, FitsBars figure11ControlHeights figure11Control scale ∧
      FitsBars figure11PuzzleHeights figure11Puzzles scale) ∧
    (∀ f scale, FitsBars figure11ControlHeights f scale → f = figure11Control) ∧
    (∀ f scale, FitsBars figure11PuzzleHeights f scale → f = figure11Puzzles) := by
  refine ⟨⟨3.25,?_,?_⟩,fun _ _ => control_counts,fun _ _ => puzzles_counts⟩ <;>
    constructor <;> first | decide +kernel | (intro i; fin_cases i <;>
      norm_num [figure11ControlHeights,figure11PuzzleHeights,figure11Control,figure11Puzzles,Matrix.cons_val_succ,abs_le])

end Thesis.StudyANCOVA
