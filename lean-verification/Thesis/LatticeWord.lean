import Std.Tactic

namespace Thesis.LatticeWord

/-- Binomial coefficients in Pascal's convention. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

private theorem choose_above : ∀ n k, n < k → choose n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose, choose_above n k (by omega), choose_above n (k + 1) (by omega)]

@[simp] theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose, ih, choose_above n (n + 1) (by omega)]

inductive Letter | a | b
  deriving DecidableEq

/-- The value at the unused origin is set to the empty word. -/
def word : Nat → Nat → List Letter
  | 0, 0 => []
  | 0, _ + 1 => [.a]
  | _ + 1, 0 => [.b]
  | u + 1, v + 1 => word u (v + 1) ++ word (u + 1) v
termination_by u v => u + v

theorem length_word (u v : Nat) (h : 0 < u + v) :
    (word u v).length = choose (u + v) u := by
  match u, v with
  | 0, 0 => omega
  | 0, v + 1 => simp [word]
  | u + 1, 0 => simp [word]
  | u + 1, v + 1 =>
    rw [word, List.length_append, length_word u (v + 1) (by omega),
      length_word (u + 1) v (by omega)]
    rw [show u + 1 + (v + 1) = (u + v + 1) + 1 by omega, choose]
    rw [show u + (v + 1) = u + v + 1 by omega,
      show u + 1 + v = u + v + 1 by omega]
termination_by u + v

theorem count_a (u v : Nat) : (word u (v + 1)).count .a = choose (u + v) u := by
  match u, v with
  | 0, v => simp [word]
  | u + 1, 0 =>
    have hb : Letter.b ≠ Letter.a := by decide
    rw [word, List.count_append, count_a u 0]
    simp [word, hb]
  | u + 1, v + 1 =>
    rw [word, List.count_append, count_a u (v + 1), count_a (u + 1) v]
    rw [show u + 1 + (v + 1) = (u + v + 1) + 1 by omega, choose]
    rw [show u + (v + 1) = u + v + 1 by omega,
      show u + 1 + v = u + v + 1 by omega]
termination_by u + v

theorem count_b (u v : Nat) : (word (u + 1) v).count .b = choose (u + v) v := by
  match u, v with
  | u, 0 => simp [word]
  | 0, v + 1 =>
    have ha : Letter.a ≠ Letter.b := by decide
    rw [word, List.count_append, count_b 0 v]
    simp [word, ha]
  | u + 1, v + 1 =>
    rw [word, List.count_append, count_b u (v + 1), count_b (u + 1) v]
    rw [show u + 1 + (v + 1) = (u + v + 1) + 1 by omega, choose, Nat.add_comm]
    rw [show u + (v + 1) = u + v + 1 by omega,
      show u + 1 + v = u + v + 1 by omega]
termination_by u + v

private theorem choose_symm (u v : Nat) : choose (u + v) u = choose (u + v) v := by
  match u, v with
  | 0, v => simp
  | u + 1, 0 => simp
  | u + 1, v + 1 =>
    rw [show u + 1 + (v + 1) = (u + v + 1) + 1 by omega]
    change choose (u + v + 1) u + choose (u + v + 1) (u + 1) =
      choose (u + v + 1) v + choose (u + v + 1) (v + 1)
    have h1 := choose_symm u (v + 1)
    have h2 := choose_symm (u + 1) v
    rw [show u + (v + 1) = u + v + 1 by omega] at h1
    rw [show u + 1 + v = u + v + 1 by omega] at h2
    omega
termination_by u + v

private theorem count_balance (u v : Nat) :
    (word u v).count .a * u = (word u v).count .b * v := by
  have ha : Letter.a ≠ Letter.b := by decide
  have hb : Letter.b ≠ Letter.a := by decide
  match u, v with
  | 0, 0 => simp
  | 0, v + 1 => simp [word, ha]
  | u + 1, 0 => simp [word, hb]
  | u + 1, v + 1 =>
    have h1 := count_balance u (v + 1)
    have h2 := count_balance (u + 1) v
    have hs : (word u (v + 1)).count .a = (word (u + 1) v).count .b := by
      rw [count_a, count_b, choose_symm]
    simp only [word, List.count_append, Nat.add_mul]
    rw [Nat.mul_succ ((word u (v + 1)).count .a), h1, h2, hs]
    rw [Nat.mul_succ ((word (u + 1) v).count .b)]
    ac_rfl
termination_by u + v

private theorem length_eq_counts (w : List Letter) :
    w.length = w.count .a + w.count .b := by
  have ha : Letter.a ≠ Letter.b := by decide
  have hb : Letter.b ≠ Letter.a := by decide
  induction w with
  | nil => rfl
  | cons letter w ih =>
    cases letter <;> simp [ha, hb] <;> omega

/-- The exact densities from `newprove`, expressed by clearing denominators. -/
theorem densities (u v : Nat) :
    (word u v).count .a * (u + v) = v * (word u v).length ∧
    (word u v).count .b * (u + v) = u * (word u v).length := by
  have h := count_balance u v
  rw [length_eq_counts]
  constructor
  · rw [Nat.mul_add, Nat.mul_add, h]
    ac_rfl
  · rw [Nat.mul_add, Nat.mul_add, ← h]
    ac_rfl

private theorem choose_pascal (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

private theorem choose_pos_of_le (n k : Nat) (h : k ≤ n) : 0 < choose n k := by
  induction n generalizing k with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    decide
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [choose]
      have hp := ih k (by omega)
      omega

private theorem choose_le_succ_of_below_middle (n k : Nat) (h : 2 * k < n) :
    choose n k ≤ choose n (k + 1) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      rw [choose_zero_right]
      exact choose_pos_of_le (n + 1) 1 (by omega)
    | succ k =>
      by_cases he : 2 * (k + 1) = n
      · have hsym := choose_symm (k + 1) (k + 2)
        rw [show k + 1 + (k + 2) = n + 1 by omega] at hsym
        exact Nat.le_of_eq hsym
      · have h₁ := ih k (by omega)
        have h₂ := ih (k + 1) (by omega)
        rw [choose_pascal n k, choose_pascal n (k + 1)]
        omega

private theorem choose_le_central_left (n k : Nat) (h : k ≤ n) :
    choose (2 * n) k ≤ choose (2 * n) n := by
  by_cases he : k = n
  · simp [he]
  · exact Nat.le_trans (choose_le_succ_of_below_middle (2 * n) k (by omega))
      (choose_le_central_left n (k + 1) (by omega))
termination_by n - k

private theorem choose_le_central (n k : Nat) (h : k ≤ 2 * n) :
    choose (2 * n) k ≤ choose (2 * n) n := by
  by_cases hk : k ≤ n
  · exact choose_le_central_left n k hk
  · have hs := choose_symm k (2 * n - k)
    rw [show k + (2 * n - k) = 2 * n by omega] at hs
    rw [hs]
    exact choose_le_central_left n (2 * n - k) (by omega)

private def partialRow (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => partialRow n k + choose n k

private theorem partialRow_step (n k : Nat) :
    partialRow n (k + 1) = partialRow n k + choose n k := rfl

private theorem partialRow_pascal (n k : Nat) :
    partialRow (n + 1) (k + 1) = partialRow n (k + 1) + partialRow n k := by
  induction k with
  | zero => simp [partialRow]
  | succ k ih =>
    rw [partialRow, ih, choose_pascal n k]
    simp only [partialRow]
    omega

private theorem completeRow_sum (n : Nat) : partialRow n (n + 1) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [partialRow_pascal, partialRow_step n (n + 1), choose_above n (n + 1) (by omega), ih,
      Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
    omega

private theorem partialRow_le (n k m : Nat) (h : ∀ i < k, choose n i ≤ m) :
    partialRow n k ≤ k * m := by
  induction k with
  | zero => simp [partialRow]
  | succ k ih =>
    rw [partialRow, Nat.succ_mul]
    exact Nat.add_le_add (ih fun i hi => h i (by omega)) (h k (by omega))

private theorem choose_le_partialRow (n i k : Nat) (h : i < k) :
    choose n i ≤ partialRow n k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [partialRow]
    by_cases he : i = k
    · rw [he]
      exact Nat.le_add_left _ _
    · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

/-- The elementary central-binomial squeeze for the diagonal length in
`newprove`. The lower bound is expressed without division. -/
theorem diagonal_length_bounds (n : Nat) (hn : 0 < n) :
    4 ^ n ≤ (2 * n + 1) * (word n n).length ∧ (word n n).length ≤ 4 ^ n := by
  rw [length_word n n (by omega), ← Nat.two_mul n]
  have hpow : 2 ^ (2 * n) = 4 ^ n := by
    rw [Nat.pow_mul]
  rw [← hpow, ← completeRow_sum]
  exact ⟨partialRow_le _ _ _ (fun i hi => choose_le_central n i (by omega)),
    choose_le_partialRow _ _ _ (by omega)⟩

end Thesis.LatticeWord
