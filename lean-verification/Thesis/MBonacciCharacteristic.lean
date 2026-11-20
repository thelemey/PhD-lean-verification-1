import Thesis.MBonacciDensity
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots

open Polynomial
open scoped BigOperators

namespace Thesis.MBonacci

/-- The m-step polynomial for the differences of consecutive prefix lengths. -/
noncomputable def gapPolynomial (m : Nat) : ℂ[X] :=
  X ^ m - ∑ j ∈ Finset.range m, X ^ j

/-- The polynomial of Fischler's recurrence for the prefix lengths. -/
noncomputable def lengthPolynomial (m : Nat) : ℂ[X] :=
  X ^ (m + 1) - 2 * X ^ m + 1

theorem lengthPolynomial_factor (m : Nat) :
    lengthPolynomial m = (X - 1) * gapPolynomial m := by
  unfold lengthPolynomial gapPolynomial
  rw [mul_sub, mul_geom_sum, pow_succ]
  ring

private theorem gapPolynomial_monic {m : Nat} (hm : 0 < m) : (gapPolynomial m).Monic := by
  apply monic_X_pow_sub
  apply lt_of_le_of_lt degree_le_natDegree
  have h : (∑ j ∈ Finset.range m, (X : ℂ[X]) ^ j).natDegree ≤ m - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    rw [natDegree_X_pow]
    have hmem := Finset.mem_range.mp hj
    omega
  exact_mod_cast h.trans_lt (by omega : m - 1 < m)

private theorem gapPolynomial_beta_root (n : Nat) :
    (gapPolynomial (n + 2)).IsRoot (beta n : ℂ) := by
  have hb := (beta_spec n).2
  unfold characteristic at hb
  unfold IsRoot gapPolynomial
  simpa only [eval_sub, eval_pow, eval_X, eval_finset_sum] using
    (show (beta n : ℂ) ^ (n + 2) - ∑ j ∈ Finset.range (n + 2), (beta n : ℂ) ^ j = 0 by
      exact_mod_cast hb)

private theorem mul_eval_derivative_X_pow (x : ℂ) {j : Nat} :
    x * ((X : ℂ[X]) ^ j).derivative.eval x = (j : ℂ) * x ^ j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [derivative_X_pow_succ, eval_mul, eval_C, eval_pow, eval_X, pow_succ]
    push_cast
    ring

private theorem gapPolynomial_derivative_beta (n : Nat) :
    (gapPolynomial (n + 2)).derivative.eval (beta n : ℂ) ≠ 0 := by
  let m := n + 2
  let x : ℂ := (beta n : ℂ)
  have hb : 1 < beta n := (beta_spec n).1
  have hr : x ^ m = ∑ j ∈ Finset.range m, x ^ j := by
    have h := gapPolynomial_beta_root n
    unfold IsRoot gapPolynomial at h
    simpa only [eval_sub, eval_pow, eval_X, eval_finset_sum, sub_eq_zero] using h
  have he :
      x * (gapPolynomial m).derivative.eval x =
        ∑ j ∈ Finset.range m, ((m : ℂ) - j) * x ^ j := by
    unfold gapPolynomial
    rw [derivative_sub, map_sum, eval_sub, eval_finset_sum, mul_sub, Finset.mul_sum,
      mul_eval_derivative_X_pow, hr, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_eval_derivative_X_pow, sub_mul]
  have hpos : 0 < ∑ j ∈ Finset.range m, ((m : ℝ) - j) * beta n ^ j := by
    apply Finset.sum_pos'
    · intro j hj
      have hj' : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hj).le
      exact mul_nonneg (sub_nonneg.mpr hj') (by positivity)
    · refine ⟨0, Finset.mem_range.mpr (by dsimp [m]; omega), ?_⟩
      simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one]
      positivity
  intro hz
  rw [hz, mul_zero] at he
  have hzero : (0 : ℝ) = ∑ j ∈ Finset.range m, ((m : ℝ) - j) * beta n ^ j := by
    dsimp only [x] at he
    exact_mod_cast he
  linarith

/-- Removing the simple dominant root β leaves a monic factor whose roots
all have strictly smaller modulus. This applies to the length recurrence,
whose extra root at 1 is also smaller than β. -/
theorem lengthPolynomial_dominant_factor (n : Nat) :
    ∃ q : ℂ[X], (lengthPolynomial (n + 2)) = (X - C (beta n : ℂ)) * q ∧
      q.Monic ∧ q.eval (beta n : ℂ) ≠ 0 ∧ ∀ z ∈ q.roots, ‖z‖ < beta n := by
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.2 (gapPolynomial_beta_root n)
  let x : ℂ := (beta n : ℂ)
  have hr' : gapPolynomial (n + 2) = (X - C x) * r := hr
  have hm : r.Monic := (monic_X_sub_C x).of_mul_monic_left
    (hr' ▸ gapPolynomial_monic (by omega : 0 < n + 2))
  have hne : r.eval x ≠ 0 := by
    have hd := gapPolynomial_derivative_beta n
    rw [hr', derivative_mul] at hd
    simpa [x] using hd
  have hβ := (beta_spec n).1
  have hx1 : x - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    dsimp only [x]
    exact_mod_cast hβ.ne'
  have hmonicOne : ((X : ℂ[X]) - 1).Monic := by
    simpa using monic_X_sub_C (1 : ℂ)
  refine ⟨(X - 1) * r, ?_, hmonicOne.mul hm, ?_, ?_⟩
  · rw [lengthPolynomial_factor, hr']
    ring
  · simpa only [eval_mul, eval_sub, eval_X, eval_one] using mul_ne_zero hx1 hne
  · intro z hz
    have hz' := isRoot_of_mem_roots hz
    unfold IsRoot at hz'
    simp only [eval_mul, eval_sub, eval_X, eval_one] at hz'
    rcases mul_eq_zero.mp hz' with hz1 | hzr
    · rw [sub_eq_zero.mp hz1, norm_one]
      exact hβ
    · have hroot : (gapPolynomial (n + 2)).eval z = 0 := by
        rw [hr', eval_mul, hzr, mul_zero]
      unfold gapPolynomial at hroot
      have hform : z ^ (n + 2) = ∑ j ∈ Finset.range (n + 2), z ^ j := by
        simpa only [eval_sub, eval_pow, eval_X, eval_finset_sum, sub_eq_zero] using hroot
      exact other_characteristic_roots_smaller n z hform (fun he => by subst z; exact hne hzr)

end Thesis.MBonacci
