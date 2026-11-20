import Thesis.ThueMorseClassification
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

namespace Thesis.ThueMorse

/-- Concatenate the digits of m with the k base-b digits of i,
allowing leading zeros in the latter. -/
theorem digitSum_aligned {b : Nat} (hb : 1 < b) (k m i : Nat) (hi : i < b ^ k) :
    digitSum b (b ^ k * m + i) = digitSum b m + digitSum b i := by
  induction k generalizing i with
  | zero =>
    have : i = 0 := by simpa using hi
    simp [this]
  | succ k ih =>
    have hb0 : 0 < b := by omega
    have hq : i / b < b ^ k := by
      apply (Nat.div_lt_iff_lt_mul hb0).2
      simpa only [pow_succ] using hi
    have hr := Nat.mod_lt i hb0
    have he : b * (i / b) + i % b = i := by rw [Nat.add_comm, Nat.mod_add_div]
    have he' : b ^ (k + 1) * m + i = b * (b ^ k * m + i / b) + i % b := by
      conv_lhs => rw [← he]
      rw [pow_succ]
      ring
    rw [he', digitSum_block hb _ _ hr, ih _ hq]
    conv_rhs => rw [← he, digitSum_block hb _ _ hr]
    omega

/-- The aligned substitution blocks of equation eq:blocks. -/
theorem word_aligned {b N : Nat} (hb : 1 < b) (k m i : Nat) (hi : i < b ^ k) :
    word b N (b ^ k * m + i) = (word b N m + digitSum b i) % N := by
  simp only [word, digitSum_aligned hb k m i hi, Nat.mod_add_mod]

theorem digitSum_le_of_lt_power {b : Nat} (hb : 1 < b) (k i : Nat) (hi : i < b ^ k) :
    digitSum b i ≤ k * (b - 1) := by
  induction k generalizing i with
  | zero =>
    have : i = 0 := by simpa using hi
    simp [this]
  | succ k ih =>
    have hb0 : 0 < b := by omega
    have hq : i / b < b ^ k := by
      apply (Nat.div_lt_iff_lt_mul hb0).2
      simpa only [pow_succ] using hi
    have hr := Nat.mod_lt i hb0
    have he : b * (i / b) + i % b = i := by rw [Nat.add_comm, Nat.mod_add_div]
    rw [← he, digitSum_block hb _ _ hr, Nat.succ_mul]
    exact Nat.add_le_add (ih _ hq) (by omega)

/-- Every digit sum between 0 and k(b-1) occurs on the k-digit block. -/
theorem digitSum_hits_of_le {b : Nat} (hb : 1 < b) (k s : Nat) (hs : s ≤ k * (b - 1)) :
    ∃ i < b ^ k, digitSum b i = s := by
  induction k generalizing s with
  | zero =>
    have : s = 0 := by simpa using hs
    exact ⟨0, by simp, by simp [this]⟩
  | succ k ih =>
    let r := min s (b - 1)
    have hr : r < b := by have h := Nat.min_le_right s (b - 1); omega
    have hsr : s - r ≤ k * (b - 1) := by
      rw [Nat.succ_mul] at hs
      dsimp only [r]
      omega
    obtain ⟨q, hq, hsq⟩ := ih _ hsr
    have hlt : b * q + r < b ^ (k + 1) := by
      rw [pow_succ, Nat.mul_comm (b ^ k) b]
      have h₁ : b * q + r < b * (q + 1) := by rw [Nat.mul_succ]; omega
      exact h₁.trans_le (Nat.mul_le_mul_left b hq)
    refine ⟨b * q + r, hlt, ?_⟩
    rw [digitSum_block hb q r hr, hsq]
    exact Nat.sub_add_cancel (Nat.min_le_left _ _)

/-- All letters occur in each substituted block once the substitution
has been iterated at least N−1 times. -/
theorem aligned_block_contains_letter {b N : Nat} (hb : 1 < b) (hN : 0 < N)
    (k m c : Nat) (hk : N - 1 ≤ k) (hc : c < N) :
    ∃ i < b ^ k, word b N (b ^ k * m + i) = c := by
  let a := word b N m
  have ha : a < N := Nat.mod_lt _ hN
  let r := (c + (N - a)) % N
  have hr : r < N := Nat.mod_lt _ hN
  have hkr : r ≤ k * (b - 1) := by
    have h := Nat.mul_le_mul_left k (show 1 ≤ b - 1 by omega)
    rw [Nat.mul_one] at h
    omega
  obtain ⟨i, hi, he⟩ := digitSum_hits_of_le hb k r hkr
  refine ⟨i, hi, ?_⟩
  rw [word_aligned hb k m i hi, he]
  change (a + (c + (N - a)) % N) % N = c
  rw [Nat.add_mod_mod, show a + (c + (N - a)) = c + N by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hc]

/-- A finite window indexed by its length. -/
def window (w : Nat → A) (k i : Nat) : Fin k → A :=
  fun j => w (i + j)

/-- Uniform recurrence in the bounded-gap form. -/
def UniformlyRecurrent (w : Nat → A) : Prop :=
  ∀ k i, ∃ L, ∀ x, ∃ j, x ≤ j ∧ j + k ≤ x + L ∧ window w k j = window w k i

/-- An occurrence is contained in two aligned blocks. Its letters
depend only on the two letters in the desubstituted word and its offset. -/
def twoBlockLetter (b N e a c t : Nat) : Nat :=
  if t < b ^ e then (a + digitSum b t) % N
  else (c + digitSum b (t - b ^ e)) % N

theorem word_in_two_blocks {b N : Nat} (hb : 1 < b) (e m t : Nat) (ht : t < 2 * b ^ e) :
    word b N (b ^ e * m + t) =
      twoBlockLetter b N e (word b N m) (word b N (m + 1)) t := by
  unfold twoBlockLetter
  split_ifs with h
  · exact word_aligned hb e m t h
  · have h' : t - b ^ e < b ^ e := by omega
    have he : b ^ e * m + t = b ^ e * (m + 1) + (t - b ^ e) := by
      rw [Nat.mul_succ]
      omega
    rw [he, word_aligned hb e _ _ h']

/-- Choose the smallest power of b which can contain a window of length k. -/
theorem exists_covering_power {b k : Nat} (hb : 1 < b) (hk : 0 < k) :
    ∃ e, k ≤ b ^ e ∧ b ^ e < b * k := by
  have hpos : 0 < b := by omega
  refine ⟨Nat.clog b k, (Nat.le_pow_iff_clog_le hb).2 le_rfl, ?_⟩
  by_cases hz : Nat.clog b k = 0
  · rw [hz, pow_zero]
    exact lt_of_lt_of_le hb (by simpa using Nat.mul_le_mul_left b hk)
  · obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hz
    rw [he, pow_succ']
    apply Nat.mul_lt_mul_of_pos_left _ hpos
    by_contra! h
    have hh := (Nat.le_pow_iff_clog_le hb).1 h
    omega

end Thesis.ThueMorse
