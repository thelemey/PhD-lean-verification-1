import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Real Set MeasureTheory Filter intervalIntegral

namespace Thesis.StudyANCOVA

/-- Student's t density up to its positive normalization constant. The constant
cancels in the two-sided test. The ANCOVA has 81 residual degrees of freedom;
the Welch degrees of freedom in §4.3 need not be integral. -/
noncomputable def studentKernel (ν x : ℝ) : ℝ :=
  1 / (1 + x ^ 2 / ν) ^ ((ν + 1) / 2 : ℝ)

noncomputable def studentTail (ν t : ℝ) : ℝ := ∫ x in Ioi t, studentKernel ν x

/-- By symmetry this is the t probability outside [-|t|, |t|]. -/
noncomputable def studentTwoSidedP (ν t : ℝ) : ℝ :=
  studentTail ν |t| / studentTail ν 0

theorem studentKernel_pos {ν : ℝ} (hν : 0 < ν) (x : ℝ) : 0 < studentKernel ν x := by
  unfold studentKernel
  positivity

theorem continuous_studentKernel {ν : ℝ} (hν : 0 < ν) : Continuous (studentKernel ν) := by
  unfold studentKernel
  apply continuous_const.div
  · apply Continuous.rpow_const (by fun_prop)
    exact fun x => Or.inl (ne_of_gt (by positivity))
  · exact fun x => (Real.rpow_pos_of_pos (by positivity) _).ne'

/-- Rational-power envelopes throughout the range of degrees of freedom used
by the two tests. They allow the comparisons with 5% to be kernel-checked. -/
theorem studentKernel_sandwich {ν : ℝ} (hlo : 80 ≤ ν) (hhi : ν ≤ 82) (x : ℝ) :
    1 / (1 + x ^ 2 / 80) ^ 42 ≤ studentKernel ν x ∧
    studentKernel ν x ≤ 1 / (1 + x ^ 2 / 82) ^ 40 := by
  have hν : 0 < ν := by linarith
  have hx := sq_nonneg x
  have base₁ : 1 + x ^ 2 / ν ≤ 1 + x ^ 2 / 80 :=
    add_le_add_left (div_le_div_of_nonneg_left hx (by norm_num) hlo) _
  have base₂ : 1 + x ^ 2 / 82 ≤ 1 + x ^ 2 / ν :=
    add_le_add_left (div_le_div_of_nonneg_left hx hν hhi) _
  have hb : 1 ≤ 1 + x ^ 2 / ν := le_add_of_nonneg_right (by positivity)
  have hexp : 0 ≤ (ν + 1) / 2 := by linarith
  unfold studentKernel
  constructor
  · apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
    calc
      _ ≤ (1 + x ^ 2 / ν) ^ (42 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb (by linarith)
      _ ≤ _ := by
        rw [show (42 : ℝ) = ((42 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        exact pow_le_pow_left₀ (by positivity) base₁ _
  · apply one_div_le_one_div_of_le (by positivity)
    calc
      _ ≤ (1 + x ^ 2 / ν) ^ (40 : ℕ) := pow_le_pow_left₀ (by positivity) base₂ _
      _ ≤ _ := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le hb
        norm_num
        linarith

private theorem majorant {ν x : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82) (hx : 6 ≤ x) :
    studentKernel ν x ≤ (1 / 1000 : ℝ) * x ^ (-2 : ℝ) := by
  have hx' : 0 < x := by linarith
  have hb : (1 + 36 / 82 : ℝ) ≤ 1 + x ^ 2 / 82 := by nlinarith [sq_nonneg (x - 6)]
  have hpower : (82000 : ℝ) ≤ (1 + x ^ 2 / 82) ^ 39 :=
    (by norm_num : (82000 : ℝ) ≤ (1 + 36 / 82 : ℝ) ^ 39).trans
      (pow_le_pow_left₀ (by norm_num) hb 39)
  have hprod := mul_le_mul hpower (show x ^ 2 / 82 ≤ 1 + x ^ 2 / 82 by linarith)
    (by positivity : 0 ≤ x ^ 2 / 82) (by positivity)
  have hden : 1000 * x ^ 2 ≤ (1 + x ^ 2 / 82) ^ 40 := by
    rw [show (40 : ℕ) = 39 + 1 by decide, pow_succ]
    linarith only [hprod]
  refine (studentKernel_sandwich hν hν' x).2.trans ?_
  rw [Real.rpow_neg hx'.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc
    _ ≤ 1 / (1000 * x ^ 2) := one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by ring

private theorem integrable_majorant :
    IntegrableOn (fun x : ℝ => (1 / 1000 : ℝ) * x ^ (-2 : ℝ)) (Ioi 6) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _

private theorem integrable_student_tail_six {ν : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82) :
    IntegrableOn (studentKernel ν) (Ioi 6) := by
  apply integrable_majorant.mono' (continuous_studentKernel (by linarith)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (6 : ℝ)) measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (studentKernel_pos (by linarith) x)]
  exact majorant hν hν' (le_of_lt hx)

theorem integrable_student_tail {ν : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82) (a : ℝ) :
    IntegrableOn (studentKernel ν) (Ioi a) := by
  by_cases ha : a ≤ 6
  · rw [← Ioc_union_Ioi_eq_Ioi ha]
    exact ((continuous_studentKernel (by linarith)).intervalIntegrable a 6).1.union
      (integrable_student_tail_six hν hν')
  · exact (integrable_student_tail_six hν hν').mono_set (Ioi_subset_Ioi (by linarith))

theorem studentTail_split {ν a b : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82) (hab : a ≤ b) :
    studentTail ν a = (∫ x in a..b, studentKernel ν x) + studentTail ν b := by
  unfold studentTail
  rw [intervalIntegral.integral_of_le hab, ← Ioc_union_Ioi_eq_Ioi hab]
  apply setIntegral_union _ measurableSet_Ioi
    ((continuous_studentKernel (by linarith)).intervalIntegrable a b).1 (integrable_student_tail hν hν' _)
  exact disjoint_left.2 fun x hx hy => (not_lt_of_ge hx.2) hy

theorem studentTail_nonneg {ν : ℝ} (hν : 0 < ν) (a : ℝ) : 0 ≤ studentTail ν a :=
  integral_nonneg fun x => (studentKernel_pos hν x).le

theorem studentTail_antitone {ν : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82) :
    Antitone (studentTail ν) := by
  intro a b h
  rw [studentTail_split hν hν' h]
  exact le_add_of_nonneg_left (intervalIntegral.integral_nonneg h
    (fun x _ => (studentKernel_pos (by linarith : 0 < ν) x).le))

theorem studentTail_six_le {ν : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82) :
    studentTail ν 6 ≤ 1 / 6000 := by
  apply (setIntegral_mono_on (integrable_student_tail_six hν hν') integrable_majorant
    measurableSet_Ioi (fun x hx => majorant hν hν' (le_of_lt hx))).trans
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
  norm_num [Real.rpow_neg_one]

/-- Normalizing the density on the whole real line and integrating over both
tails gives the same probability as the one-sided ratio used in the tests. -/
theorem studentTwoSidedP_eq_density_probability {ν : ℝ} (hν : 80 ≤ ν) (hν' : ν ≤ 82)
    (t : ℝ) : studentTwoSidedP ν t =
      (∫ x in {x : ℝ | |t| < |x|}, studentKernel ν x) / (∫ x, studentKernel ν x) := by
  have even (x : ℝ) : studentKernel ν (-x) = studentKernel ν x := by simp [studentKernel]
  have habs (x : ℝ) : studentKernel ν |x| = studentKernel ν x := by simp [studentKernel]
  have den := integral_comp_abs (f := studentKernel ν)
  simp only [habs] at den
  have hset : {x : ℝ | |t| < |x|} = Iio (-|t|) ∪ Ioi |t| := by
    ext x
    change |t| < |x| ↔ x < -|t| ∨ |t| < x
    rw [lt_abs]
    constructor <;> rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl h
  have hl : IntegrableOn (studentKernel ν) (Iio (-|t|)) := by
    have h : IntegrableOn (studentKernel ν) (Ioi (- -|t|)) :=
      integrable_student_tail hν hν' _
    simpa only [even] using h.comp_neg_Iio
  have hd : Disjoint (Iio (-|t|)) (Ioi |t|) := disjoint_left.2 (by
    intro x hx hx'
    change x < -|t| at hx
    change |t| < x at hx'
    linarith [abs_nonneg t])
  have he := integral_comp_neg_Ioi |t| (studentKernel ν)
  simp only [even, integral_Iic_eq_integral_Iio] at he
  rw [hset, setIntegral_union hd measurableSet_Ioi hl (integrable_student_tail hν hν' _),
    ← he, den]
  unfold studentTwoSidedP studentTail
  ring

end Thesis.StudyANCOVA
