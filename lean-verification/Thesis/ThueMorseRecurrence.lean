import Thesis.ThueMorseBlocks
import Mathlib.Data.Fintype.Pi

namespace Thesis.ThueMorse

/-- Each factor of W occurs inside every aligned block of level
k+r+N−1, where b^k covers the factor and b^r covers the two letters
of the desubstituted source occurrence. -/
theorem factor_in_aligned_blocks {b N : Nat} (hb : 1 < b) (hN : 0 < N)
    (k i : Nat) :
    ∃ T, ∀ m, ∃ v, v + k ≤ b ^ T ∧
      window (word b N) k (b ^ T * m + v) = window (word b N) k i := by
  let e := Nat.clog b k
  let B := b ^ e
  have hB : 0 < B := Nat.pow_pos (by omega)
  have hk : k ≤ B := (Nat.le_pow_iff_clog_le hb).2 le_rfl
  let t := i / B
  let r := Nat.clog b (t + 2)
  have hr : t + 2 ≤ b ^ r := (Nat.le_pow_iff_clog_le hb).2 le_rfl
  have hi : i + k ≤ b ^ (e + r) := by
    have hdiv : B * t + i % B = i := by rw [Nat.add_comm, Nat.mod_add_div]
    have hmod := Nat.mod_lt i hB
    calc
      i + k ≤ B * (t + 2) := by
        rw [Nat.mul_add, Nat.mul_two]
        omega
      _ ≤ b ^ (e + r) := by rw [pow_add]; exact Nat.mul_le_mul_left _ hr
  refine ⟨e + r + (N - 1), fun m => ?_⟩
  obtain ⟨j, hj, hzero⟩ :=
    aligned_block_contains_letter hb hN (N - 1) m 0 le_rfl hN
  refine ⟨b ^ (e + r) * j + i, ?_, ?_⟩
  · calc
      b ^ (e + r) * j + i + k ≤ b ^ (e + r) * (j + 1) := by
        rw [Nat.mul_succ]
        omega
      _ ≤ b ^ (e + r + (N - 1)) := by
        rw [pow_add b (e + r) (N - 1)]
        exact Nat.mul_le_mul_left _ hj
  · funext l
    have hl : i + l < b ^ (e + r) := by have hh := l.isLt; omega
    have he : b ^ (e + r + (N - 1)) * m + (b ^ (e + r) * j + i) + l =
        b ^ (e + r) * (b ^ (N - 1) * m + j) + (i + l) := by rw [pow_add]; ring
    simp only [window, he]
    rw [word_aligned hb _ _ _ hl, hzero, Nat.zero_add]
    rfl

/-- The aligned blocks yield the explicit gap bound 2b^T from the
proof of uniform recurrence in thm:dynWb. -/
theorem uniformlyRecurrent_word {b N : Nat} (hb : 1 < b) (hN : 0 < N) :
    UniformlyRecurrent (word b N) := by
  intro k i
  obtain ⟨T, hT⟩ := factor_in_aligned_blocks hb hN k i
  let B := b ^ T
  have hB : 0 < B := Nat.pow_pos (by omega)
  refine ⟨2 * B, fun x => ?_⟩
  let m := x / B + 1
  have hm : x ≤ B * m ∧ B * m ≤ x + B := by
    have h := Nat.mod_add_div x B
    have h' := Nat.mod_lt x hB
    dsimp [m]
    rw [Nat.mul_succ]
    omega
  obtain ⟨v, hv, he⟩ := hT m
  refine ⟨B * m + v, by omega, ?_, he⟩
  change v + k ≤ B at hv
  omega

/-- The corollary to the twisted critical exponent excludes every
eventual period using arbitrarily long zero-twist windows. -/
theorem not_eventually_periodic_word {b N : Nat} (hb : 1 < b) (hN : 0 < N)
    (haper : ¬ N ∣ b - 1) :
    ¬ ∃ i m : Nat, 0 < m ∧ ∀ t : Nat, word b N (i + t + m) = word b N (i + t) := by
  rintro ⟨i, m, hm, he⟩
  let k := max 2 (2 * b / positiveTwist N 0) + 1
  have hr : StrongRepeat b N k 0 := by
    refine ⟨i, m, hm, fun t _ => ?_⟩
    rw [he, Nat.add_zero]
    exact (Nat.mod_mod _ _).symm
  have h := critical_bound_of_repeat hb hN haper hr
  dsimp [k] at h
  omega

/-- The same digit-sum word with its finite alphabet as the codomain. -/
def finiteWord (b N : Nat) (hN : 0 < N) (i : Nat) : Fin N :=
  ⟨word b N i, Nat.mod_lt _ hN⟩

theorem uniformlyRecurrent_finiteWord {b N : Nat} (hb : 1 < b) (hN : 0 < N) :
    UniformlyRecurrent (finiteWord b N hN) := by
  intro k i
  obtain ⟨L, hL⟩ := uniformlyRecurrent_word hb hN k i
  refine ⟨L, fun x => ?_⟩
  obtain ⟨j, hj, hlen, he⟩ := hL x
  refine ⟨j, hj, hlen, ?_⟩
  funext l
  apply Fin.ext
  exact congrFun he l

end Thesis.ThueMorse
