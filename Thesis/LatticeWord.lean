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

end Thesis.LatticeWord
