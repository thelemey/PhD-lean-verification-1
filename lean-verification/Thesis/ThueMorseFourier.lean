import Thesis.ThueMorseBlocks
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Arg
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace Thesis.ThueMorse

private theorem sum_aligned_digits (f : Nat → ℂ) (b q : Nat) :
    (∑ i ∈ Finset.range (b * q), f i) =
      ∑ i ∈ Finset.range q, ∑ j ∈ Finset.range b, f (b * i + j) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

noncomputable def digitKernel (b : Nat) (z : ℂ) : ℂ :=
  ∑ d ∈ Finset.range b, z ^ d

/-- The digit-sum polynomial on the aligned b^k block is the kth
power of the single-digit geometric polynomial. -/
theorem digit_polynomial_pow {b : Nat} (hb : 1 < b) (k : Nat) (z : ℂ) :
    (∑ i ∈ Finset.range (b ^ k), z ^ digitSum b i) = digitKernel b z ^ k := by
  induction k with
  | zero => simp [Finset.sum_range_one]
  | succ k ih =>
    rw [pow_succ' b, sum_aligned_digits]
    have h : (∑ i ∈ Finset.range (b ^ k), ∑ r ∈ Finset.range b,
        z ^ digitSum b (b * i + r)) =
        ∑ i ∈ Finset.range (b ^ k), z ^ digitSum b i * digitKernel b z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [digitKernel, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [digitSum_block hb _ _ (Finset.mem_range.1 hr), pow_add]
    rw [h, ← Finset.sum_mul, ih, pow_succ]

private theorem root_filter {N : Nat} {ζ : ℂ} (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N)
    (s c : Nat) (hc : c < N) :
    (∑ l ∈ Finset.range N, (ζ ^ l) ^ s / (ζ ^ l) ^ c) =
      if s % N = c then (N : ℂ) else 0 := by
  have hζ0 : ζ ≠ 0 := by
    intro he
    have h := hζ.pow_eq_one
    simp [he, hN.ne'] at h
  let z := ζ ^ ((s : ℤ) - (c : ℤ))
  have hzN : z ^ N = 1 := by
    dsimp [z]
    rw [zpow_sub₀ hζ0, div_pow, zpow_natCast, zpow_natCast,
      pow_right_comm ζ s N, pow_right_comm ζ c N, hζ.pow_eq_one]
    simp
  have hz1 : z = 1 ↔ s % N = c := by
    change ζ ^ ((s : ℤ) - (c : ℤ)) = 1 ↔ s % N = c
    rw [hζ.zpow_eq_one_iff_dvd, ← Nat.modEq_iff_dvd]
    exact ⟨fun he => (show s % N = c % N from he.symm).trans (Nat.mod_eq_of_lt hc), fun he =>
      show c % N = s % N by rw [Nat.mod_eq_of_lt hc, he]⟩
  have he (l : Nat) : (ζ ^ l) ^ s / (ζ ^ l) ^ c = z ^ l := by
    dsimp [z]
    rw [zpow_sub₀ hζ0, zpow_natCast, zpow_natCast, div_pow,
      pow_right_comm ζ s l, pow_right_comm ζ c l]
  simp only [he]
  by_cases h : s % N = c
  · simp [h, hz1.2 h]
  · rw [if_neg h, geom_sum_eq (fun hn => h (hz1.1 hn)), hzN]
    simp

/-- The number of occurrences of c in the block obtained by substituting
the starting letter a exactly k times. -/
def blockLetterCount (b N k a c : Nat) : Nat :=
  ∑ i ∈ Finset.range (b ^ k), if (a + digitSum b i) % N = c then 1 else 0

/-- The finite roots-of-unity filter, including the term for the
trivial character. -/
theorem block_count_fourier {b N : Nat} (hb : 1 < b) (hN : 0 < N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (k a c : Nat) (hc : c < N) :
    (N : ℂ) * (blockLetterCount b N k a c : ℂ) =
      ∑ l ∈ Finset.range N, ((ζ ^ l) ^ a / (ζ ^ l) ^ c) * digitKernel b (ζ ^ l) ^ k := by
  have hcount (i : Nat) :
      (N : ℂ) * ((if (a + digitSum b i) % N = c then 1 else 0 : Nat) : ℂ) =
        ∑ l ∈ Finset.range N, (ζ ^ l) ^ (a + digitSum b i) / (ζ ^ l) ^ c := by
    rw [root_filter hN hζ _ _ hc]
    split_ifs <;> simp
  simp only [blockLetterCount, Nat.cast_sum, Finset.mul_sum, hcount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← digit_polynomial_pow hb k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring

private theorem digitKernel_norm_lt {b : Nat} (hb : 1 < b) {z : ℂ} (hz : ‖z‖ = 1)
    (hne : z ≠ 1) : ‖digitKernel b z‖ < b := by
  have hn : ¬ SameRay ℝ (1 : ℂ) z := by
    intro h
    have he := h.norm_smul_eq
    have hz1 : z = (1 : ℂ) := by simpa [hz] using he
    exact hne hz1
  have hpair : ‖(1 : ℂ) + z‖ < 2 := by
    simpa [hz, one_add_one_eq_two] using norm_add_lt_of_not_sameRay hn
  have hr := norm_sum_le (Finset.range (b - 2)) (fun j => z ^ (2 + j))
  simp only [norm_pow, hz, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hr
  have hb' : 2 + (b - 2) = b := by omega
  unfold digitKernel
  conv_lhs => rw [← hb', Finset.sum_range_add]
  have h2 : (∑ i ∈ Finset.range 2, z ^ i) = 1 + z := by
    norm_num [Finset.sum_range_succ]
  rw [h2]
  apply (norm_add_le _ _).trans_lt
  have hbc : (↑(b - 2) : ℝ) + 2 = b := by exact_mod_cast (by omega : b - 2 + 2 = b)
  linarith

/-- The maximum modulus of the nontrivial digit kernels is strictly
below the block length b. -/
theorem exists_digit_kernel_bound {b N : Nat} (hb : 1 < b) (hN : 1 < N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    ∃ β : ℝ, 0 ≤ β ∧ β < b ∧
      ∀ l : Nat, 0 < l → l < N → ‖digitKernel b (ζ ^ l)‖ ≤ β := by
  let S := Finset.Ico 1 N
  have hS : S.Nonempty := ⟨1, Finset.mem_Ico.2 ⟨le_rfl, hN⟩⟩
  obtain ⟨l, hl, hh⟩ := Finset.exists_max_image S (fun l => ‖digitKernel b (ζ ^ l)‖) hS
  have hbounds := Finset.mem_Ico.1 hl
  have hnorm : ‖ζ ^ l‖ = 1 := by
    rw [norm_pow, hζ.norm'_eq_one (by omega : N ≠ 0), one_pow]
  have hne : ζ ^ l ≠ 1 := fun h => by
    have hdiv := (hζ.pow_eq_one_iff_dvd l).1 h
    have hle := Nat.le_of_dvd (by omega : 0 < l) hdiv
    omega
  refine ⟨‖digitKernel b (ζ ^ l)‖, norm_nonneg _, digitKernel_norm_lt hb hnorm hne, ?_⟩
  exact fun j hj hj' => hh j (Finset.mem_Ico.2 ⟨hj, hj'⟩)

/-- The nontrivial Fourier terms bound the discrepancy in any aligned
block by β^k, uniformly in its starting letter. -/
theorem block_count_discrepancy {b N : Nat} (hb : 1 < b) (hN : 1 < N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {β : ℝ} (hβ : 0 ≤ β)
    (hker : ∀ l : Nat, 0 < l → l < N → ‖digitKernel b (ζ ^ l)‖ ≤ β)
    (k a c : Nat) (hc : c < N) :
    |(blockLetterCount b N k a c : ℝ) - ((b : ℝ) ^ k) / N| ≤ β ^ k := by
  let term (l : Nat) := ((ζ ^ l) ^ a / (ζ ^ l) ^ c) * digitKernel b (ζ ^ l) ^ k
  let S := ∑ l ∈ Finset.range (N - 1), term (l + 1)
  have hterm : ∀ l ∈ Finset.range (N - 1), ‖term (l + 1)‖ ≤ β ^ k := by
    intro l hl
    have hh := Finset.mem_range.1 hl
    simp only [term, norm_mul, norm_div, norm_pow, hζ.norm'_eq_one (by omega : N ≠ 0),
      one_pow, div_one, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (hker _ (by omega) (by omega)) _
  have hS : ‖S‖ ≤ (↑(N - 1) : ℝ) * β ^ k := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ l ∈ Finset.range (N - 1), ‖term (l + 1)‖) ≤
          ∑ _l ∈ Finset.range (N - 1), β ^ k := Finset.sum_le_sum hterm
      _ = _ := by simp [nsmul_eq_mul]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0C : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hsum := block_count_fourier hb (by omega : 0 < N) hζ k a c hc
  change (N : ℂ) * (blockLetterCount b N k a c : ℂ) = ∑ l ∈ Finset.range N, term l at hsum
  have hsplit : (∑ l ∈ Finset.range N, term l) = S + term 0 := by
    conv_lhs => rw [show N = N - 1 + 1 by omega, Finset.sum_range_succ']
  have htrivial : term 0 = (b : ℂ) ^ k := by
    simp [term, digitKernel, nsmul_eq_mul]
  rw [hsplit, htrivial] at hsum
  have he : (blockLetterCount b N k a c : ℂ) - (b : ℂ) ^ k / N = S / N := by
    apply (eq_div_iff hN0C).2
    rw [sub_mul, div_mul_cancel₀ _ hN0C]
    linear_combination hsum
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  rw [he, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hN0).2
  exact hS.trans (by
    rw [mul_comm (β ^ k)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.sub_le N 1)) (pow_nonneg hβ _))

end Thesis.ThueMorse
