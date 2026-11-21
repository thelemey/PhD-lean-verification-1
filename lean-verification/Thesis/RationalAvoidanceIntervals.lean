import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open Set Metric

namespace Thesis.SturmianDensity

/-- Distinct rational centers with denominators at most Q are separated
by at least one over Q squared. The fractions need not be reduced. -/
theorem rational_center_separation {p p' : ℤ} {q q' Q : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hQ : q ≤ Q) (hQ' : q' ≤ Q)
    (hne : (p : ℝ) / q ≠ (p' : ℝ) / q') :
    1 / (Q : ℝ) ^ 2 ≤ |(p : ℝ) / q - (p' : ℝ) / q'| := by
  let u : ℤ := p * (q' : ℤ) - p' * (q : ℤ)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have he : (p : ℝ) / q - (p' : ℝ) / q' = (u : ℝ) / ((q : ℝ) * q') := by
    dsimp only [u]
    push_cast
    field_simp [hqr.ne', hqr'.ne']
    ring
  have hu : u ≠ 0 := by
    intro h
    apply hne (sub_eq_zero.1 _)
    rw [he, h, Int.cast_zero, zero_div]
  have hlow : (1 : ℝ) ≤ |(u : ℝ)| := by exact_mod_cast Int.one_le_abs hu
  have hprod : 0 < (q : ℝ) * q' := mul_pos hqr hqr'
  have hle : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul (by exact_mod_cast hQ) (by exact_mod_cast hQ') hqr'.le
      (by positivity)
  rw [he, abs_div, abs_of_pos hprod]
  exact (one_div_le_one_div_of_le hprod hle).trans
    (div_le_div_of_nonneg_right hlow hprod.le)

namespace Avoidance

noncomputable def scale (S : ℕ) : ℝ := (S : ℝ) ^ 2

noncomputable def width (S n : ℕ) : ℝ := 1 / (4 * scale S ^ (n + 1))

noncomputable def constant (S : ℕ) : ℝ := 1 / (16 * scale S ^ 2)

noncomputable def margin (S n : ℕ) : ℝ := width S (n + 1) / 4

theorem scale_gt_one {S : ℕ} (hS : 1 < S) : 1 < scale S := by
  have h : (1 : ℝ) < S := by exact_mod_cast hS
  unfold scale
  nlinarith

theorem width_pos {S : ℕ} (hS : 1 < S) (n : ℕ) : 0 < width S n := by
  have h := (scale_gt_one hS).trans_le' zero_le_one
  unfold width
  positivity

theorem constant_pos {S : ℕ} (hS : 1 < S) : 0 < constant S := by
  have h := (scale_gt_one hS).trans_le' zero_le_one
  unfold constant
  positivity

theorem width_step {S : ℕ} (hS : 1 < S) (n : ℕ) :
    scale S * width S (n + 1) = width S n := by
  have h := (scale_gt_one hS).trans_le' zero_le_one
  unfold width
  rw [pow_succ (scale S) (n + 1), ← mul_assoc, ← div_div, ← mul_div_assoc,
    mul_div_cancel_left₀ _ h.ne']

theorem width_le {S : ℕ} (hS : 1 < S) (n : ℕ) : width S (n + 1) ≤ width S n := by
  rw [← width_step hS n]
  have := mul_le_mul_of_nonneg_right (scale_gt_one hS).le (width_pos hS (n + 1)).le
  simpa only [one_mul] using this

theorem margin_le_width {S : ℕ} (hS : 1 < S) (n : ℕ) :
    width S n + 2 * margin S n < 4 * width S n := by
  unfold margin
  linarith [width_le hS n, width_pos hS n]

private theorem denominator_square (S n : ℕ) :
    ((S ^ n : ℕ) : ℝ) ^ 2 = scale S ^ n := by
  simp only [Nat.cast_pow, scale, ← pow_mul, Nat.mul_comm]

theorem separation_width {S : ℕ} (hS : 1 < S) (n : ℕ) :
    1 / (((S ^ (n + 1) : ℕ) : ℝ) ^ 2) = 4 * width S n := by
  rw [denominator_square, width]
  have hs : 0 < scale S := (scale_gt_one hS).trans_le' zero_le_one
  field_simp [hs.ne']

theorem band_error_le_margin {S : ℕ} (hS : 1 < S) (n q : ℕ) (hq : S ^ n ≤ q) :
    constant S / (q : ℝ) ^ 2 ≤ margin S n := by
  have hp : 0 < scale S := (scale_gt_one hS).trans_le' zero_le_one
  have hden : scale S ^ n ≤ (q : ℝ) ^ 2 := by
    rw [← denominator_square]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hq) _
  have hr : margin S n = constant S / scale S ^ n := by
    unfold margin width constant
    rw [div_div, div_div, show n + 1 + 1 = 2 + n by omega, pow_add]
    congr 1
    ring
  rw [hr]
  exact div_le_div_of_nonneg_left (constant_pos hS).le (pow_pos hp _) hden

/-- A parent interval can contain the neighborhoods of at most one
rational center from the current band, even after enlarging its ends. -/
theorem dangerous_centers_eq {S : ℕ} (hS : 1 < S) (n : ℕ) (x : ℝ)
    {p p' : ℤ} {q q' : ℕ} (hq : S ^ n ≤ q) (hq' : S ^ n ≤ q')
    (hQ : q < S ^ (n + 1)) (hQ' : q' < S ^ (n + 1))
    (hP : (p : ℝ) / q ∈ Icc (x - margin S n) (x + width S n + margin S n))
    (hP' : (p' : ℝ) / q' ∈ Icc (x - margin S n) (x + width S n + margin S n)) :
    (p : ℝ) / q = (p' : ℝ) / q' := by
  by_contra hne
  have hpos : 0 < S ^ n := Nat.pow_pos (zero_lt_one.trans hS)
  have hsep := rational_center_separation (hpos.trans_le hq) (hpos.trans_le hq') hQ.le hQ'.le hne
  rw [separation_width hS] at hsep
  have hnear : |(p : ℝ) / q - (p' : ℝ) / q'| ≤ width S n + 2 * margin S n :=
    abs_le.2 ⟨by linarith [hP.1, hP'.2], by linarith [hP.2, hP'.1]⟩
  exact (not_le_of_gt (margin_le_width hS n)) (hsep.trans hnear)

end Avoidance
end Thesis.SturmianDensity
