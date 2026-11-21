import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

namespace Thesis.StudyANCOVA

variable {n : ℕ}

noncomputable def mean (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

noncomputable def centered (x : Fin n → ℝ) (i : Fin n) : ℝ := x i - mean x

noncomputable def ss (x : Fin n → ℝ) : ℝ := ∑ i, centered x i ^ 2

noncomputable def cross (x y : Fin n → ℝ) : ℝ := ∑ i, centered x i * centered y i

private theorem sum_centered (hn : 0 < n) (x : Fin n → ℝ) : ∑ i, centered x i = 0 := by
  simp only [centered, mean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [mul_div_cancel₀ _ hnR, sub_self]

private theorem mean_sub (x y : Fin n → ℝ) :
    mean (fun i => y i - x i) = mean y - mean x := by
  unfold mean
  rw [Finset.sum_sub_distrib, sub_div]

/-- Paired gain deviations recover the within-group pre/post cross product. -/
theorem cross_eq_of_gain (x y : Fin n → ℝ) :
    cross x y = (ss x + ss y - ss (fun i => y i - x i)) / 2 := by
  have h (i : Fin n) : centered (fun j => y j - x j) i ^ 2 =
      centered x i ^ 2 + centered y i ^ 2 - 2 * (centered x i * centered y i) := by
    simp only [centered, mean_sub]
    ring
  unfold ss cross
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The common-slope regression in §4.3, with a group effect for group B. -/
noncomputable def loss (xA yA xB yB : Fin n → ℝ) (a g b : ℝ) : ℝ :=
  (∑ i, (yA i - (a + b * xA i)) ^ 2) + ∑ i, (yB i - (a + g + b * xB i)) ^ 2

theorem group_loss (hn : 0 < n) (x y : Fin n → ℝ) (a b : ℝ) :
    ∑ i, (y i - (a + b * x i)) ^ 2 =
      ss y - 2 * b * cross x y + b ^ 2 * ss x +
        n * (mean y - a - b * mean x) ^ 2 := by
  let d := mean y - a - b * mean x
  let r := fun i => centered y i - b * centered x i
  have he (i : Fin n) : (y i - (a + b * x i)) ^ 2 = r i ^ 2 + 2 * d * r i + d ^ 2 := by
    dsimp only [r, d, centered]
    ring
  have hsum : ∑ i, r i = 0 := by
    simp only [r, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_centered hn, mul_zero, sub_zero]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr (i : Fin n) : r i ^ 2 = centered y i ^ 2 - 2 * b * (centered x i * centered y i) +
      b ^ 2 * centered x i ^ 2 := by
    dsimp only [r]
    ring
  simp_rw [hr]
  simp only [ss, cross, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, d]

/-- The fitted group coefficient is the post-test mean difference adjusted
by the pre-test difference times the pooled within-group slope. -/
theorem loss_minimizer (hn : 0 < n) (xA yA xB yB : Fin n → ℝ)
    (hx : 0 < ss xA + ss xB) :
    let b := (cross xA yA + cross xB yB) / (ss xA + ss xB)
    let a := mean yA - b * mean xA
    let g := mean yB - mean yA - b * (mean xB - mean xA)
    ∀ u v w : ℝ, loss xA yA xB yB a g b ≤ loss xA yA xB yB u v w := by
  intro b a g u v w
  let x := ss xA + ss xB
  let y := ss yA + ss yB
  have hb : b * x = cross xA yA + cross xB yB := by
    dsimp only [b, x]
    exact div_mul_cancel₀ _ hx.ne'
  have hdecomp (u v w : ℝ) : loss xA yA xB yB u v w =
      y - b ^ 2 * x + (w - b) ^ 2 * x +
        n * (mean yA - u - w * mean xA) ^ 2 +
        n * (mean yB - (u + v) - w * mean xB) ^ 2 := by
    rw [loss, group_loss hn, group_loss hn]
    dsimp only [x, y] at hb ⊢
    linear_combination 2 * w * hb
  rw [hdecomp, hdecomp]
  have ha : mean yA - a - b * mean xA = 0 := by dsimp only [a]; ring
  have hg : mean yB - (a + g) - b * mean xB = 0 := by dsimp only [a, g]; ring
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, add_zero, ha, hg]
  have hx' : 0 ≤ x := hx.le
  have hnonneg : 0 ≤ (w - b) ^ 2 * x := by positivity
  linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n)
    (sq_nonneg (mean yA - u - w * mean xA)),
    mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (mean yB - (u + v) - w * mean xB))]

/-- The residual sum of squares at the common-slope fit. -/
theorem loss_at_fit (hn : 0 < n) (xA yA xB yB : Fin n → ℝ)
    (hx : 0 < ss xA + ss xB) :
    let xx := ss xA + ss xB
    let xy := cross xA yA + cross xB yB
    let b := xy / xx
    let a := mean yA - b * mean xA
    let g := mean yB - mean yA - b * (mean xB - mean xA)
    loss xA yA xB yB a g b = ss yA + ss yB - xy ^ 2 / xx := by
  intro xx xy b a g
  have hb : b * xx = xy := div_mul_cancel₀ _ hx.ne'
  have hba : mean yA - a - b * mean xA = 0 := by dsimp only [a]; ring
  have hbb : mean yB - (a + g) - b * mean xB = 0 := by dsimp only [a, g]; ring
  have he : xy ^ 2 / xx = b * xy := by
    change xy ^ 2 / xx = (xy / xx) * xy
    rw [div_mul_eq_mul_div, pow_two]
  rw [loss, group_loss hn, group_loss hn, hba, hbb, he]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  dsimp only [xx, xy] at hb ⊢
  linear_combination b * hb

private theorem cross_eq_sum_centered_mul (hn : 0 < n) (x y : Fin n → ℝ) :
    cross x y = ∑ i, centered x i * y i := by
  unfold cross
  simp only [show ∀ i, centered y i = y i - mean y from fun _ => rfl,
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_centered hn, zero_mul, sub_zero]

private theorem sum_sq_weights (hn : 0 < n) (x : Fin n → ℝ) (a b : ℝ) :
    ∑ i, (a + b * centered x i) ^ 2 = n * a ^ 2 + b ^ 2 * ss x := by
  have he (i : Fin n) : (a + b * centered x i) ^ 2 = a ^ 2 +
      (2 * a * b) * centered x i + b ^ 2 * centered x i ^ 2 := by ring
  simp_rw [he]
  simp only [ss, Finset.sum_add_distrib, ← Finset.mul_sum, sum_centered hn,
    mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The adjusted contrast is linear in post-test scores. The sum of squares
of its weights is its variance multiplier for independent equal-variance errors. -/
theorem adjustedContrast_weights (hn : 0 < n) (xA yA xB yB : Fin n → ℝ)
    (hx : 0 < ss xA + ss xB) :
    let xx := ss xA + ss xB
    let dx := mean xB - mean xA
    let weightA := fun i => -1 / n + (-dx / xx) * centered xA i
    let weightB := fun i => 1 / n + (-dx / xx) * centered xB i
    (∑ i, weightA i * yA i) + (∑ i, weightB i * yB i) =
        mean yB - mean yA - (cross xA yA + cross xB yB) / xx * dx ∧
      (∑ i, weightA i ^ 2) + (∑ i, weightB i ^ 2) = 2 / n + dx ^ 2 / xx := by
  intro xx dx wa wb
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  constructor
  · dsimp only [wa, wb]
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← cross_eq_sum_centered_mul hn, mean]
    ring
  · dsimp only [wa, wb]
    rw [sum_sq_weights hn, sum_sq_weights hn]
    have h1 : (n : ℝ) * (1 / n) ^ 2 = 1 / n := by
      field_simp [hnR]
      ring
    have h2 : (n : ℝ) * (-1 / n) ^ 2 = 1 / n := by rw [neg_div, neg_sq, h1]
    rw [h1, h2]
    have hcancel : (-dx / xx) ^ 2 * xx = dx ^ 2 / xx := by
      field_simp [hx.ne']
      ring
    dsimp only [xx] at hcancel
    linear_combination hcancel

end Thesis.StudyANCOVA
