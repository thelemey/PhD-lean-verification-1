import Thesis.Fibonacci
import Thesis.PalindromeFactors

namespace Thesis.TernaryWord

open PalindromeFactors

/-- The symbols `none`, `some .b`, and `some .a` represent 0, 1, and 2. -/
def word : Nat → List (Option Fibonacci.Letter)
  | 0 => [none, some .b]
  | 1 => [none, some .a]
  | n + 2 => word (n + 1) ++ word n

/-- The finite morphism identity in `lem:Ystructure`. -/
theorem word_succ_eq_interleave : ∀ n, word (n + 1) = interleave (Fibonacci.word n)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [word, word_succ_eq_interleave (n + 1), word_succ_eq_interleave n,
      Fibonacci.word, interleave_append]

theorem word_prefix_succ (n : Nat) (hn : 0 < n) : word n <+: word (n + 1) := by
  cases n with
  | zero => omega
  | succ n =>
    change word (n + 1) <+: word (n + 1) ++ word n
    exact List.prefix_append _ _

/-- The nesting begins with y₁. The initial stage y₀ is a separate word. -/
theorem word_zero_not_prefix_one : ¬ word 0 <+: word 1 := by
  simp [word]

theorem length_word (n : Nat) : (word n).length = 2 * Fibonacci.fib (n + 1) := by
  cases n with
  | zero => rfl
  | succ n => rw [word_succ_eq_interleave, length_interleave, Fibonacci.word_length]

/-- In the separate initial case y₀ = 01 the only nonempty palindromic
factors are its two individual letters, as counted directly in §3.6. -/
theorem word_zero_enumeration :
    Enumerates (word 0) [[none], [some Fibonacci.Letter.b]] := by
  refine ⟨by decide, ?_⟩
  intro v
  cases v with
  | nil => simp [PalindromicFactor]
  | cons a v =>
    cases v with
    | nil => simp [word, PalindromicFactor, List.infix_cons_iff]
    | cons b v =>
      cases v with
      | nil =>
        simp [word, PalindromicFactor, List.infix_cons_iff]
        rintro rfl rfl
        decide
      | cons c v =>
        simp [word, PalindromicFactor, List.infix_cons_iff]

/-- The ternary richness deduction in `thm:Yrich`, using the classical
richness of finite Fibonacci words as its only word-specific premise. -/
theorem rich_word_of_fibonacci (hFib : ∀ n, Rich (Fibonacci.word n)) (n : Nat) :
    Rich (word n) := by
  have hpos (k : Nat) : Rich (word (k + 1)) := by
    rw [word_succ_eq_interleave]
    exact rich_of_infix ((rich_framed_iff _).2 (hFib k))
      (List.prefix_append _ _).isInfix
  cases n with
  | zero => exact ⟨_, word_zero_enumeration, rfl⟩
  | succ n => exact hpos n

theorem factor_count_of_fibonacci (hFib : ∀ n, Rich (Fibonacci.word n)) (n : Nat) :
    ∃ ps, Enumerates (word n) ps ∧ ps.length = 2 * Fibonacci.fib (n + 1) := by
  simpa only [Rich, length_word] using rich_word_of_fibonacci hFib n

/-- The language of the infinite ternary word is the union of the languages
of the finite words `word n`. Any finite factor in that union is rich. -/
theorem rich_factor_of_fibonacci (hFib : ∀ n, Rich (Fibonacci.word n))
    (v : List (Option Fibonacci.Letter)) (hv : ∃ n, v <:+: word n) : Rich v := by
  obtain ⟨n, hn⟩ := hv
  exact rich_of_infix (rich_word_of_fibonacci hFib n) hn

end Thesis.TernaryWord
