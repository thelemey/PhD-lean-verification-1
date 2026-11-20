import Thesis.FibonacciBinet
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace Thesis.Fibonacci

noncomputable def millinPartial (m N : Nat) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), (1 : ℝ) / fib (m * 2 ^ (i + 1))

noncomputable def millinLimit (φ : ℝ) (m : Nat) : ℝ :=
  previousRatio m - 1 / φ + (1 - (-1 : ℝ) ^ m) / fib (2 * m)

private theorem fib_real_ge_one {n : Nat} (hn : 0 < n) : (1 : ℝ) ≤ fib n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact_mod_cast fib_positive k

/-- The exact remainder in `thm:millin`, obtained by inserting the
Binet expression for the last ratio into the partial sum identity. -/
theorem millin_remainder {φ ψ : ℝ} (hsum : φ + ψ = 1) (hprod : φ * ψ = -1)
    (m : Nat) (hm : 0 < m) (N : Nat) :
    millinLimit φ m - millinPartial m N =
      -(ψ ^ (m * 2 ^ (N + 1) - 1)) / (φ * (fib (m * 2 ^ (N + 1)) : ℝ)) := by
  let M := m * 2 ^ (N + 1)
  have hM : 0 < M := Nat.mul_pos hm (Nat.two_pow_pos _)
  have hr := previousRatio_binet hsum hprod (M - 1)
  rw [show M - 1 + 1 = M by omega] at hr
  unfold millinLimit millinPartial
  rw [millin_partial_sum m hm N]
  change _ - (previousRatio (K := ℝ) m - previousRatio M +
    (1 - (-1 : ℝ) ^ m) / fib (2 * m)) = _
  rw [hr, neg_div]
  ring

/-- An explicit doubly exponential bound, stronger than the stated
big-O bound. Its exponent is (M=m2^{N+1}). -/
theorem millin_remainder_bound {φ ψ : ℝ} (hsum : φ + ψ = 1) (hprod : φ * ψ = -1)
    (hφ : 1 < φ) (m : Nat) (hm : 0 < m) (N : Nat) :
    |millinLimit φ m - millinPartial m N| ≤ (φ⁻¹) ^ (m * 2 ^ (N + 1)) := by
  let M := m * 2 ^ (N + 1)
  have hM : 0 < M := Nat.mul_pos hm (Nat.two_pow_pos _)
  have hφ0 : 0 < φ := by linarith
  have hF := fib_real_ge_one hM
  have hF0 : 0 < (fib M : ℝ) := by linarith
  have ⟨hpos, _, hψ⟩ := reciprocal_and_conjugate hprod hφ
  rw [millin_remainder hsum hprod m hm N]
  change |-(ψ ^ (M - 1)) / (φ * (fib M : ℝ))| ≤ (φ⁻¹) ^ M
  rw [abs_div, abs_neg, abs_pow, hψ, abs_neg, abs_of_pos hpos,
    abs_of_pos (mul_pos hφ0 hF0)]
  apply (div_le_iff₀ (mul_pos hφ0 hF0)).2
  have hcancel : (φ⁻¹) ^ M * φ = (φ⁻¹) ^ (M - 1) := by
    calc
      _ = (φ⁻¹) ^ (M - 1 + 1) * φ := by rw [show M - 1 + 1 = M by omega]
      _ = (φ⁻¹) ^ (M - 1) := by rw [pow_succ, mul_assoc, inv_mul_cancel₀ hφ0.ne', mul_one]
  rw [← mul_assoc, hcancel]
  exact le_mul_of_one_le_right (pow_nonneg hpos.le _) hF

/-- The infinite Millin sum, stated as convergence of the partial sums
in the usual epsilon definition. -/
theorem millin_converges {φ ψ : ℝ} (hsum : φ + ψ = 1) (hprod : φ * ψ = -1)
    (hφ : 1 < φ) (m : Nat) (hm : 0 < m) :
    ∀ ε > (0 : ℝ), ∃ K : Nat, ∀ N ≥ K,
      |millinLimit φ m - millinPartial m N| < ε := by
  intro ε hε
  have ⟨hpos, hlt, _⟩ := reciprocal_and_conjugate hprod hφ
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε hlt
  refine ⟨K, ?_⟩
  intro N hN
  have hpow : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
  have hmul : 2 ^ (N + 1) ≤ m * 2 ^ (N + 1) := by
    simpa using Nat.mul_le_mul_right (2 ^ (N + 1)) (show 1 ≤ m by omega)
  have hstrict : K < m * 2 ^ (N + 1) := by omega
  exact lt_of_le_of_lt (millin_remainder_bound hsum hprod hφ m hm N)
    ((pow_lt_pow_right_of_lt_one₀ hpos hlt hstrict).trans hK)

noncomputable def evenShiftPartial (r N : Nat) : ℝ :=
  ∑ i ∈ Finset.range N, (1 : ℝ) / ((fib (i + 1) : ℝ) * fib (i + 1 + 2 * r))

noncomputable def evenShiftLimit (r : Nat) : ℝ :=
  (∑ i ∈ Finset.range r, (1 : ℝ) / ((fib (2 * i + 1) : ℝ) * fib (2 * i + 2))) / fib (2 * r)

private theorem ratio_error_bound {φ ψ : ℝ} (hsum : φ + ψ = 1) (hprod : φ * ψ = -1)
    (hφ : 1 < φ) {n : Nat} (hn : 0 < n) :
    |ratio (K := ℝ) n - φ| ≤ (φ⁻¹) ^ n := by
  have hf := fib_real_ge_one hn
  have hf0 : 0 < (fib n : ℝ) := by linarith
  have h := fib_next_sub_phi_mul hsum hprod n
  have he : ratio (K := ℝ) n - φ = ψ ^ n / fib n := by
    unfold ratio
    field_simp [hf0.ne']
    linarith
  have ⟨hpos, _, hψ⟩ := reciprocal_and_conjugate hprod hφ
  rw [he, abs_div, abs_pow, hψ, abs_neg, abs_of_pos hpos, abs_of_pos hf0]
  exact div_le_self (pow_nonneg hpos.le _) hf

private theorem alternating_constant_sum (φ : ℝ) (N r : Nat) :
    (∑ i ∈ Finset.range (2 * r), (-1 : ℝ) ^ (N + i + 1) * φ) = 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, zero_add,
      show N + (2 * r + 1) + 1 = (N + 2 * r + 1) + 1 by omega, pow_succ]
    ring

/-- The alternating tail in the proof of `prop:sum2r` tends to zero:
after cancelling the constant (φ) in pairs, each residual is bounded
by the Binet error. -/
theorem alternating_tail_bound {φ ψ : ℝ} (hsum : φ + ψ = 1) (hprod : φ * ψ = -1)
    (hφ : 1 < φ) (N r : Nat) :
    |∑ i ∈ Finset.range (2 * r), signedRatio (K := ℝ) (N + i + 1)| ≤
      ((2 * r : Nat) : ℝ) * (φ⁻¹) ^ (N + 1) := by
  have ⟨hpos, hlt, _⟩ := reciprocal_and_conjugate hprod hφ
  have hterm (i : Nat) :
      signedRatio (K := ℝ) (N + i + 1) - (-1 : ℝ) ^ (N + i + 1) * φ =
        (-1 : ℝ) ^ (N + i + 1) * (ratio (K := ℝ) (N + i + 1) - φ) := by
    simp only [signedRatio, mul_sub]
  have htail : (∑ i ∈ Finset.range (2 * r), signedRatio (K := ℝ) (N + i + 1)) =
      ∑ i ∈ Finset.range (2 * r),
        (-1 : ℝ) ^ (N + i + 1) * (ratio (K := ℝ) (N + i + 1) - φ) := by
    simp only [← hterm, Finset.sum_sub_distrib, alternating_constant_sum, sub_zero]
  rw [htail]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _ ∈ Finset.range (2 * r), (φ⁻¹) ^ (N + 1) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact (ratio_error_bound hsum hprod hφ (by omega)).trans
        (pow_le_pow_of_le_one hpos.le hlt.le (by omega))
    _ = _ := by simp [nsmul_eq_mul]

/-- The series with even shift in `prop:sum2r`, in the epsilon definition
of convergence of its partial sums. -/
theorem even_shift_converges {φ ψ : ℝ} (hsum : φ + ψ = 1) (hprod : φ * ψ = -1)
    (hφ : 1 < φ) (r : Nat) (hr : 0 < r) :
    ∀ ε > (0 : ℝ), ∃ K : Nat, ∀ N ≥ K,
      |evenShiftPartial r N - evenShiftLimit r| < ε := by
  intro ε hε
  have ⟨hpos, hlt, _⟩ := reciprocal_and_conjugate hprod hφ
  have h2r : 0 < ((2 * r : Nat) : ℝ) := by exact_mod_cast (show 0 < 2 * r by omega)
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hε h2r) hlt
  refine ⟨K, ?_⟩
  intro N hN
  have hf := fib_real_ge_one (n := 2 * r) (by omega)
  have hf0 : 0 < (fib (2 * r) : ℝ) := by linarith
  have he : evenShiftPartial r N - evenShiftLimit r =
      -(∑ i ∈ Finset.range (2 * r), signedRatio (K := ℝ) (N + i + 1)) / fib (2 * r) := by
    have h := even_shift_partial_sum (K := ℝ) r N
    unfold evenShiftPartial evenShiftLimit
    field_simp [hf0.ne']
    linear_combination h
  rw [he, abs_div, abs_neg, abs_of_pos hf0]
  apply (div_le_self (abs_nonneg _) hf).trans_lt
  apply (alternating_tail_bound hsum hprod hφ N r).trans_lt
  have hN' := (pow_lt_pow_right_of_lt_one₀ hpos hlt (show K < N + 1 by omega)).trans hK
  have hh := (lt_div_iff₀ h2r).1 hN'
  simpa [mul_comm] using hh

/-- Both limits of `thm1Asymptotic`, by the explicit Binet error estimate. -/
theorem framed_densities_converge {φ ψ : ℝ} (hsum : φ + ψ = 1)
    (hprod : φ * ψ = -1) (hφ : 1 < φ) :
    ∀ ε > (0 : ℝ), ∃ K : Nat, ∀ m ≥ K,
      |((framed m).count .a : ℝ) / (framed m).length - 1 / φ| < ε ∧
      |((framed m).count .b : ℝ) / (framed m).length - (φ⁻¹) ^ 2| < ε := by
  intro ε hε
  have ⟨hpos, hlt, hψ⟩ := reciprocal_and_conjugate hprod hφ
  let C := 2 * (φ - ψ) / (φ * (1 - φ⁻¹))
  have hC : 0 < C := by
    dsimp only [C]
    rw [hψ]
    apply div_pos
    · linarith
    · exact mul_pos (by linarith) (sub_pos.mpr hlt)
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hε hC) hlt
  refine ⟨K, ?_⟩
  intro m hm
  have hexp : (φ⁻¹) ^ (m + 2) < ε / C :=
    (pow_lt_pow_right_of_lt_one₀ hpos hlt (show K < m + 2 by omega)).trans hK
  have hε' : C * (φ⁻¹) ^ (m + 2) < ε := by
    rw [mul_comm]
    exact (lt_div_iff₀ hC).1 hexp
  have ha := (framed_density_exponential_bound hsum hprod hφ m).trans_lt hε'
  exact ⟨ha, by simpa only [framed_second_density_error hsum hprod hφ m] using ha⟩

end Thesis.Fibonacci
