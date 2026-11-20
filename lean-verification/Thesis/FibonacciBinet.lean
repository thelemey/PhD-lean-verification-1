import Thesis.FibonacciTelescoping
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Thesis.Fibonacci

private theorem root_recurrence (x : ℝ) (hx : x ^ 2 = x + 1) (n : Nat) :
    x ^ (n + 2) = x ^ n + x ^ (n + 1) := by
  rw [pow_add x n 2, hx, mul_add, mul_one, pow_succ]
  ring

/-- Binet's formula, with the two roots and their distinctness explicit. -/
theorem binet {φ ψ : ℝ} (hφ : φ ^ 2 = φ + 1) (hψ : ψ ^ 2 = ψ + 1)
    (hneq : φ ≠ ψ) : ∀ n : Nat, (fib n : ℝ) = (φ ^ n - ψ ^ n) / (φ - ψ)
  | 0 => by norm_num [fib]
  | 1 => by
    norm_num [fib, sub_ne_zero.mpr hneq]
  | n + 2 => by
    rw [fib, Nat.cast_add, binet hφ hψ hneq n, binet hφ hψ hneq (n + 1),
      root_recurrence φ hφ n, root_recurrence ψ hψ n, ← add_div]
    ring

private theorem roots_sq {φ ψ : ℝ} (hsum : φ + ψ = 1) (hprod : φ * ψ = -1) :
    φ ^ 2 = φ + 1 ∧ ψ ^ 2 = ψ + 1 := by
  have ha := congrArg (φ * ·) hsum
  have hb := congrArg (· * ψ) hsum
  simp only [mul_add, add_mul, mul_one, one_mul, hprod, ← sq] at ha hb
  constructor <;> linarith

private theorem roots_distinct {φ ψ : ℝ} (hprod : φ * ψ = -1) : φ ≠ ψ := by
  intro he
  rw [← he, ← sq] at hprod
  linarith [sq_nonneg φ]

/-- The step (F_{n+1}-φF_n=ψ^n) obtained from Binet's formula, as in
the proofs of `lem:fibA` and `thm1Asymptotic`. -/
theorem fib_next_sub_phi_mul {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (n : Nat) :
    (fib (n + 1) : ℝ) - φ * (fib n : ℝ) = ψ ^ n := by
  have ⟨hφ, hψ⟩ := roots_sq hsum hprod
  have hneq := roots_distinct hprod
  rw [binet hφ hψ hneq (n + 1), binet hφ hψ hneq n, pow_succ, pow_succ]
  field_simp [sub_ne_zero.mpr hneq]
  ring

/-- D'Ocagne's determinant by the Binet calculation in `lem:docagne`.
The factors are rearranged before using `φψ=-1`. -/
theorem docagne_from_binet {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (k m : Nat) :
    (fib (k + m) : ℝ) * (fib (k + 1) : ℝ) -
        (fib (k + m + 1) : ℝ) * (fib k : ℝ) =
      (-1 : ℝ) ^ k * (fib m : ℝ) := by
  have ⟨hφ, hψ⟩ := roots_sq hsum hprod
  have hneq := roots_distinct hprod
  calc
    _ = (φ ^ k * ψ ^ k) * (φ ^ m - ψ ^ m) / (φ - ψ) := by
      simp only [binet hφ hψ hneq, pow_add, pow_one]
      field_simp [sub_ne_zero.mpr hneq]
      ring
    _ = _ := by rw [← mul_pow, hprod, binet hφ hψ hneq m, mul_div_assoc]

/-- The exact real quotient identity in `lem:fibA`, with (n+1)
in place of the thesis's positive index (n). -/
theorem previousRatio_binet {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (n : Nat) :
    previousRatio (K := ℝ) (n + 1) =
      1 / φ - ψ ^ n / (φ * (fib (n + 1) : ℝ)) := by
  have hφ : φ ≠ 0 := by
    intro h
    simp [h] at hprod
  have hf : (fib (n + 1) : ℝ) ≠ 0 := by
    have hp : 0 < fib (n + 1) := by
      induction n with
      | zero => decide
      | succ n ih => change 0 < fib n + fib (n + 1); omega
    exact_mod_cast hp.ne'
  have h := fib_next_sub_phi_mul hsum hprod n
  unfold previousRatio
  rw [show n + 1 - 1 = n by omega]
  field_simp [hφ, hf]
  have hh : φ * (fib n : ℝ) = (fib (n + 1) : ℝ) - ψ ^ n := by linarith
  rw [← mul_assoc, mul_comm (fib n : ℝ) φ, hh]

/-- The real identity (φ^{-2}=2-φ) used in `thm1Asymptotic`. -/
theorem golden_inverse_square {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) : (φ⁻¹) ^ 2 = 2 - φ := by
  have hφ : φ ≠ 0 := by intro h; simp [h] at hprod
  have hs := (roots_sq hsum hprod).1
  rw [inv_pow]
  apply (inv_eq_one_div _).trans ?_
  apply (div_eq_iff (pow_ne_zero _ hφ)).2
  calc
    1 = 2 + φ - φ ^ 2 := by linarith
    _ = (2 - φ) * (φ + 1) := by ring
    _ = (2 - φ) * φ ^ 2 := by rw [hs]

theorem reciprocal_and_conjugate {φ ψ : ℝ}
    (hprod : φ * ψ = -1) (hφ : 1 < φ) :
    0 < φ⁻¹ ∧ φ⁻¹ < 1 ∧ ψ = -φ⁻¹ := by
  have hp : 0 < φ := by linarith
  refine ⟨inv_pos.mpr hp, inv_lt_one_of_one_lt₀ hφ, ?_⟩
  have h : ψ = (-1 : ℝ) / φ := (eq_div_iff hp.ne').2 (by simpa [mul_comm] using hprod)
  simpa [neg_div, one_div] using h

/-- The error formula in `thm1Asymptotic`, now with real divisions.
It follows from Binet and (φ^{-2}=2-φ) as in the thesis. -/
theorem framed_density_error_real {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (hφ : 1 < φ) (m : Nat) :
    ((framed m).count .a : ℝ) / (framed m).length - 1 / φ =
      -((φ⁻¹) ^ 2 + ψ ^ (m + 1)) / (φ * ((fib (m + 2) : ℝ) + 2)) := by
  have hn : φ ≠ 0 := (show 0 < φ by linarith).ne'
  have hf : (fib (m + 2) : ℝ) + 2 ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) (fib (m + 2))]
  have hb := fib_next_sub_phi_mul hsum hprod (m + 1)
  rw [framed_count_a, framed_length]
  push_cast
  rw [golden_inverse_square hsum hprod, ← hb]
  field_simp [hn, hf]
  ring

/-- The numerator of the positive error term in `thm1Asymptotic`. -/
theorem framed_error_term_pos {φ ψ : ℝ} (hprod : φ * ψ = -1)
    (hφ : 1 < φ) {m : Nat} (hm : 1 ≤ m) :
    0 < (φ⁻¹) ^ 2 + ψ ^ (m + 1) := by
  have ⟨hpos, hlt, he⟩ := reciprocal_and_conjugate hprod hφ
  rcases eq_or_lt_of_le hm with rfl | hm
  · have hp := pow_pos hpos 2
    exact add_pos_of_pos_of_nonneg hp (sq_nonneg ψ)
  · have hpow : (φ⁻¹) ^ (m + 1) < (φ⁻¹) ^ 2 :=
      pow_lt_pow_right_of_lt_one₀ hpos hlt (by omega)
    have hnorm : |ψ ^ (m + 1)| = (φ⁻¹) ^ (m + 1) := by
      rw [abs_pow, he, abs_neg, abs_of_pos hpos]
    have hlo := neg_abs_le (ψ ^ (m + 1))
    rw [hnorm] at hlo
    linarith

theorem framed_density_lt {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (hφ : 1 < φ) {m : Nat} (hm : 1 ≤ m) :
    ((framed m).count .a : ℝ) / (framed m).length < 1 / φ := by
  apply sub_lt_zero.mp
  rw [framed_density_error_real hsum hprod hφ]
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos (framed_error_term_pos hprod hφ hm)
  · have : 0 < φ := by linarith
    exact mul_pos this (by linarith [Nat.cast_nonneg (α := ℝ) (fib (m + 2))])

/-- The finite lower bound on Fibonacci growth needed for the error
estimate in `thm1Asymptotic`. It comes from Binet's formula by bounding
the conjugate term by one in absolute value. -/
theorem binet_growth_lower {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (hφ : 1 < φ) (n : Nat) :
    (1 - φ⁻¹) * φ ^ (n + 1) ≤ (φ - ψ) * (fib (n + 1) : ℝ) := by
  have ⟨hg, hg1, hψ⟩ := reciprocal_and_conjugate hprod hφ
  have hφ0 : 0 < φ := by linarith
  have hψlt : ψ < 0 := by rw [hψ]; linarith
  have hc : 0 < φ - ψ := by linarith
  have habs : |ψ ^ (n + 1)| ≤ 1 := by
    rw [abs_pow, hψ, abs_neg, abs_of_pos hg]
    exact pow_le_one₀ hg.le hg1.le
  have hp : 1 ≤ φ ^ n := one_le_pow₀ hφ.le
  have hcancel : φ⁻¹ * φ ^ (n + 1) = φ ^ n := by
    rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ hφ0.ne', one_mul]
  have hu := le_abs_self (ψ ^ (n + 1))
  rw [binet (roots_sq hsum hprod).1 (roots_sq hsum hprod).2
      (roots_distinct hprod), mul_div_cancel₀ _ hc.ne', sub_mul, one_mul, hcancel]
  linarith

/-- An explicit bound of order (1/F_{m+2}) for the framed density error. -/
theorem framed_density_error_bound {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (hφ : 1 < φ) (m : Nat) :
    |((framed m).count .a : ℝ) / (framed m).length - 1 / φ| ≤
      2 / (φ * ((fib (m + 2) : ℝ) + 2)) := by
  have ⟨hg, hg1, hψ⟩ := reciprocal_and_conjugate hprod hφ
  have hφ0 : 0 < φ := by linarith
  have hf : 0 < (fib (m + 2) : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) (fib (m + 2))]
  rw [framed_density_error_real hsum hprod hφ, abs_div, abs_neg, abs_of_pos (mul_pos hφ0 hf)]
  apply (div_le_div_iff_of_pos_right (mul_pos hφ0 hf)).2
  calc
    _ ≤ |(φ⁻¹) ^ 2| + |ψ ^ (m + 1)| := abs_add_le _ _
    _ ≤ 2 := by
      rw [abs_of_nonneg (pow_nonneg hg.le _), abs_pow, hψ, abs_neg, abs_of_pos hg]
      have h1 : (φ⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hg.le hg1.le
      have h2 : (φ⁻¹) ^ (m + 1) ≤ 1 := pow_le_one₀ hg.le hg1.le
      linarith

/-- The exponential error estimate in `thm1Asymptotic`, with an explicit
constant and with the Binet lower bound for the denominator. -/
theorem framed_density_exponential_bound {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (hφ : 1 < φ) (m : Nat) :
    |((framed m).count .a : ℝ) / (framed m).length - 1 / φ| ≤
      (2 * (φ - ψ) / (φ * (1 - φ⁻¹))) * (φ⁻¹) ^ (m + 2) := by
  have ⟨hg, hg1, hψ⟩ := reciprocal_and_conjugate hprod hφ
  have hφ0 : 0 < φ := by linarith
  have hc : 0 < φ - ψ := by rw [hψ]; linarith
  have hdiff : 0 < 1 - φ⁻¹ := sub_pos.mpr hg1
  have hf : 0 < (fib (m + 2) : ℝ) := by exact_mod_cast fib_positive (m + 1)
  have hlow := binet_growth_lower hsum hprod hφ (m + 1)
  have hpow : 0 < φ ^ (m + 2) := pow_pos hφ0 _
  have hden :
      (φ * ((1 - φ⁻¹) * φ ^ (m + 2))) ≤ (φ * ((fib (m + 2) : ℝ) + 2)) * (φ - ψ) := by
    have hbig := mul_le_mul_of_nonneg_left hlow hφ0.le
    calc
      _ ≤ φ * ((φ - ψ) * fib (m + 2)) := hbig
      _ = (φ * fib (m + 2)) * (φ - ψ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hφ0.le) hc.le
  apply (framed_density_error_bound hsum hprod hφ m).trans
  rw [inv_pow]
  have he : (2 * (φ - ψ) / (φ * (1 - φ⁻¹))) * (φ ^ (m + 2))⁻¹ =
      2 * (φ - ψ) / (φ * ((1 - φ⁻¹) * φ ^ (m + 2))) := by
    field_simp [hφ0.ne', hdiff.ne', hpow.ne']
  rw [he]
  apply (div_le_div_iff₀ (mul_pos hφ0 (by linarith)) (mul_pos hφ0 (mul_pos hdiff hpow))).2
  nlinarith only [hden]

/-- The two letters exhaust the framed word, so their relative
frequencies sum to one, as in `thm1Asymptotic`. -/
theorem framed_density_complement (m : Nat) :
    ((framed m).count .b : ℝ) / (framed m).length =
      1 - ((framed m).count .a : ℝ) / (framed m).length := by
  rw [framed_count_a, framed_count_b, framed_length]
  push_cast
  have hpos : 0 < (fib (m + 2) : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) (fib (m + 2))]
  have hrec : (fib (m + 2) : ℝ) = (fib m : ℝ) + fib (m + 1) := by
    rw [fib, Nat.cast_add]
  field_simp [hpos.ne']
  rw [hrec]
  ring

/-- The absolute error for the second density equals the absolute error
for the first, because their targets also sum to one. -/
theorem framed_second_density_error {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (hφ : 1 < φ) (m : Nat) :
    |((framed m).count .b : ℝ) / (framed m).length - (φ⁻¹) ^ 2| =
    |((framed m).count .a : ℝ) / (framed m).length - 1 / φ| := by
  have ⟨_, _, hψ⟩ := reciprocal_and_conjugate hprod hφ
  rw [hψ] at hsum
  have hcomp : (φ⁻¹) ^ 2 = 1 - 1 / φ := by
    rw [golden_inverse_square (show φ + ψ = 1 by rwa [hψ]) hprod, one_div]
    linarith
  rw [framed_density_complement, hcomp, ← abs_neg]
  congr 1
  ring

end Thesis.Fibonacci
