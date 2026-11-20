import Std.Tactic

namespace Thesis.Fibonacci

inductive Letter | a | b
  deriving DecidableEq

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | m + 2 => fib m + fib (m + 1)

def word : Nat → List Letter
  | 0 => [.a]
  | 1 => [.a, .b]
  | m + 2 => word (m + 1) ++ word m

def framed (m : Nat) : List Letter := .a :: word m ++ [.b]

theorem word_length : ∀ m, (word m).length = fib (m + 2)
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
    rw [word, List.length_append, word_length, word_length]
    change fib (m + 3) + fib (m + 2) = fib (m + 2) + fib (m + 3)
    exact Nat.add_comm _ _

theorem word_count_a : ∀ m, (word m).count .a = fib (m + 1)
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
    rw [word, List.count_append, word_count_a, word_count_a]
    change fib (m + 2) + fib (m + 1) = fib (m + 1) + fib (m + 2)
    exact Nat.add_comm _ _

theorem word_count_b : ∀ m, (word m).count .b = fib m
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
    rw [word, List.count_append, word_count_b, word_count_b, fib]
    exact Nat.add_comm _ _

theorem framed_length (m : Nat) : (framed m).length = fib (m + 2) + 2 := by
  simp [framed, word_length, Nat.add_assoc]

theorem framed_count_a (m : Nat) : (framed m).count .a = fib (m + 1) + 1 := by
  have h : Letter.b ≠ Letter.a := by decide
  simp [framed, h, word_count_a]

theorem framed_count_b (m : Nat) : (framed m).count .b = fib m + 1 := by
  have h : Letter.a ≠ Letter.b := by decide
  simp [framed, h, word_count_b]

private def millionths (count length : Nat) : Nat :=
  (2 * 1000000 * count + length) / (2 * length)

private def row (m : Nat) : Nat × Nat × Nat × Nat :=
  (millionths ((framed m).count .a) (framed m).length,
   millionths ((framed m).count .b) (framed m).length,
   millionths ((word m).count .a) (word m).length,
   millionths ((word m).count .b) (word m).length)

/-- The six finite rows of `tab002densitiesASm`, rounded to millionths. -/
theorem table_rows :
    [3, 5, 7, 9, 11, 13].map row =
      [(571429, 428571, 600000, 400000), (600000, 400000, 615385, 384615),
       (611111, 388889, 617647, 382353), (615385, 384615, 617978, 382022),
       (617021, 382979, 618026, 381974), (617647, 382353, 618033, 381967)] := by
  simp only [List.map_cons, List.map_nil, row, framed_count_a, framed_count_b,
    framed_length, word_count_a, word_count_b, word_length]
  decide

end Thesis.Fibonacci
