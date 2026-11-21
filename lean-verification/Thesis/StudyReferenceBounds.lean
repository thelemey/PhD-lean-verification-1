import Thesis.StudentTails

open Real Set MeasureTheory intervalIntegral

namespace Thesis.StudyANCOVA

/-! Rigorous bounds for the two-sided Student probabilities used in §4.3.
On [0,6] integrate the decreasing bounding densities on cells of width 1/20.
Endpoint values are rounded outwards to multiples of 1/100000 by integer division.
The remaining integral is bounded separately. -/

private noncomputable def grid (i : ℕ) : ℝ := i / 20

private def weight (b e i : ℕ) : ℕ :=
  (100000 * (400 * b) ^ e) / (400 * b + i ^ 2) ^ e

private theorem weight_bounds (b e i : ℕ) (hb : 0 < b) :
    (weight b e i : ℝ) / 100000 ≤ 1 / (1 + grid i ^ 2 / b) ^ e ∧
    1 / (1 + grid i ^ 2 / b) ^ e ≤ ((weight b e i : ℝ) + 1) / 100000 := by
  let A := 400 * b
  let B := A + i ^ 2
  have hB : 0 < B ^ e := by dsimp [A, B]; positivity
  have hlow := Nat.div_mul_le_self (100000 * A ^ e) (B ^ e)
  have hhigh := Nat.lt_mul_div_succ (100000 * A ^ e) hB
  change weight b e i * B ^ e ≤ _ at hlow
  change _ < B ^ e * (weight b e i + 1) at hhigh
  have hlow' : (weight b e i : ℝ) * (B : ℝ) ^ e ≤ 100000 * (A : ℝ) ^ e := by
    exact_mod_cast hlow
  have hhigh' : 100000 * (A : ℝ) ^ e ≤ (B : ℝ) ^ e * ((weight b e i : ℝ) + 1) := by
    exact_mod_cast hhigh.le
  have hden : (0 : ℝ) < (B : ℝ) ^ e := by exact_mod_cast hB
  have hratio : 1 / (1 + grid i ^ 2 / b) ^ e = (A : ℝ) ^ e / (B : ℝ) ^ e := by
    have hA : (1 + grid i ^ 2 / b) = (B : ℝ) / A := by
      dsimp only [A, B, grid]
      push_cast
      field_simp
      ring
    rw [hA, div_pow, one_div_div]
  rw [hratio]
  constructor
  · exact (div_le_div_iff₀ (by norm_num) hden).2 (by linarith)
  · exact (div_le_div_iff₀ hden (by norm_num)).2 (by linarith)

private def lowerWeight (k : ℕ) := weight 80 42 (k+1)
private def upperWeight (k : ℕ) := weight 82 40 k + 1

private theorem grid_step (k : ℕ) : grid (k+1) = grid k + 1 / 20 := by
  simp [grid, add_div]

private theorem cell_bounds {ν : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82) (k : ℕ) :
    (lowerWeight k : ℝ) / 2000000 ≤ ∫ x in grid k..grid (k+1), studentKernel ν x ∧
    (∫ x in grid k..grid (k+1), studentKernel ν x) ≤ (upperWeight k : ℝ) / 2000000 := by
  let a := grid k
  let b := grid (k+1)
  have has : b = a + 1 / 20 := grid_step k
  have ha : 0 ≤ a := by dsimp [a, grid]; positivity
  have hab : a ≤ b := by linarith
  have hfi := (continuous_studentKernel (show 0 < ν by linarith)).intervalIntegrable (μ := volume) a b
  have low (x : ℝ) (hx : x ∈ Icc a b) :
      (lowerWeight k : ℝ) / 100000 ≤ studentKernel ν x := by
    apply (weight_bounds 80 42 (k+1) (by decide)).1.trans
    apply le_trans _ (studentKernel_sandwich hν hν' x).1
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have hs := pow_le_pow_left₀ (ha.trans hx.1) hx.2 2
    change 1 + x ^ 2 / 80 ≤ 1 + b ^ 2 / 80
    linarith
  have up (x : ℝ) (hx : x ∈ Icc a b) :
      studentKernel ν x ≤ (upperWeight k : ℝ) / 100000 := by
    apply (studentKernel_sandwich hν hν' x).2.trans
    change _ ≤ ((weight 82 40 k + 1 : ℕ) : ℝ) / 100000
    push_cast
    apply le_trans _ (weight_bounds 82 40 k (by decide)).2
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have hs := pow_le_pow_left₀ ha hx.1 2
    change 1 + a ^ 2 / 82 ≤ 1 + x ^ 2 / 82
    linarith
  have hl := intervalIntegral.integral_mono_on hab (intervalIntegrable_const) hfi low
  have hu := intervalIntegral.integral_mono_on hab hfi (intervalIntegrable_const) up
  simp only [intervalIntegral.integral_const, smul_eq_mul, has] at hl hu
  change _ ≤ (∫ x in a..b, studentKernel ν x) ∧ (∫ x in a..b, studentKernel ν x) ≤ _
  rw [has]
  constructor <;> linarith

private def weights (f : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => weights f a n + f (a+n)

private theorem mesh_bounds {ν : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82) (a n : ℕ) :
    (weights lowerWeight a n : ℝ) / 2000000 ≤ ∫ x in grid a..grid (a+n), studentKernel ν x ∧
    (∫ x in grid a..grid (a+n), studentKernel ν x) ≤ (weights upperWeight a n : ℝ) / 2000000 := by
  induction n with
  | zero => simp [weights]
  | succ n ih =>
    have hc := cell_bounds hν hν' (a+n)
    have cont := continuous_studentKernel (show 0 < ν by linarith)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (cont.intervalIntegrable (μ := volume) (grid a) (grid (a+n))) (cont.intervalIntegrable (μ := volume) (grid (a+n)) (grid (a+n+1)))
    simp only [weights, Nat.cast_add]
    rw [← Nat.add_assoc, ← hadd]
    constructor <;> linarith [ih.1, ih.2, hc.1, hc.2]

set_option maxRecDepth 8192 in
/-- All degrees of freedom between 80 and 82: the two-sided 5% threshold
lies strictly between 1.8 and 2.1, including the nonintegral Welch cases. -/
theorem study_student_p_cutoffs {ν : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82) :
    (∀ t : ℝ, |t| ≤ 1.8 → 0.05 < studentTwoSidedP ν t) ∧
    (∀ t : ℝ, 2.1 ≤ |t| → studentTwoSidedP ν t < 0.05) := by
  have area := mesh_bounds hν hν' 0 120
  have left := (mesh_bounds hν hν' 36 84).1
  have right := (mesh_bounds hν hν' 42 78).2
  have g0 : grid 0 = 0 := by norm_num [grid]
  have g36 : grid 36 = 1.8 := by norm_num [grid]
  have g42 : grid 42 = 2.1 := by norm_num [grid]
  have g120 : grid 120 = 6 := by norm_num [grid]
  change _ ≤ (∫ x in (grid 0)..(grid 120), studentKernel ν x) ∧
    (∫ x in (grid 0)..(grid 120), studentKernel ν x) ≤ _ at area
  change _ ≤ (∫ x in (grid 36)..(grid 120), studentKernel ν x) at left
  change (∫ x in (grid 42)..(grid 120), studentKernel ν x) ≤ _ at right
  rw [g0, g120] at area
  rw [g36, g120] at left
  rw [g42, g120] at right
  have lowerArea : (2400000 : ℝ) ≤ weights lowerWeight 0 120 := by
    exact_mod_cast (show 2400000 ≤ weights lowerWeight 0 120 by decide)
  have upperArea : (weights upperWeight 0 120 : ℝ) ≤ 2620000 := by
    exact_mod_cast (show weights upperWeight 0 120 ≤ 2620000 by decide)
  have lowerLeft : (160000 : ℝ) ≤ weights lowerWeight 36 84 := by
    exact_mod_cast (show 160000 ≤ weights lowerWeight 36 84 by decide)
  have upperRight : (weights upperWeight 42 78 : ℝ) ≤ 116000 := by
    exact_mod_cast (show weights upperWeight 42 78 ≤ 116000 by decide)
  have ht0 := studentTail_nonneg (show 0 < ν by linarith) 6
  have ht6 := studentTail_six_le hν hν'
  have hA := studentTail_split hν hν' (by norm_num : (0:ℝ) ≤ 6)
  have hL := studentTail_split hν hν' (by norm_num : (1.8:ℝ) ≤ 6)
  have hR := studentTail_split hν hν' (by norm_num : (2.1:ℝ) ≤ 6)
  have hl : 1.2 ≤ studentTail ν 0 := by linarith [area.1, lowerArea]
  have hu : studentTail ν 0 < 1.32 := by linarith [area.2, upperArea]
  have positive : 0 < studentTail ν 0 := by linarith
  constructor
  · intro t ht
    apply (lt_div_iff₀ positive).2
    have hmono := studentTail_antitone hν hν' ht
    linarith [lowerLeft]
  · intro t ht
    apply (div_lt_iff₀ positive).2
    have hmono := studentTail_antitone hν hν' ht
    linarith [upperRight]

end Thesis.StudyANCOVA
