import Thesis.FibonacciRichness
import Thesis.TernaryWord
import Thesis.WordPrefixLimits

namespace Thesis.TernaryWord

open PalindromeFactors WordPrefixLimits

/-- The finite assertion of thm:Yrich, via its original separator proof. -/
theorem rich_word (n : Nat) : Rich (word n) :=
  rich_word_of_fibonacci Fibonacci.rich_word n

theorem palindromic_factor_count (n : Nat) :
    ∃ ps, Enumerates (word n) ps ∧ ps.length = 2 * Fibonacci.fib (n + 1) :=
  factor_count_of_fibonacci Fibonacci.rich_word n

private theorem word_length_pos : ∀ n, 0 < (word n).length
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    rw [word, List.length_append]
    exact Nat.add_pos_left (word_length_pos (n + 1)) _

private theorem word_covers_index : ∀ n, n < (word (n + 1)).length
  | 0 => by decide
  | n + 1 => by
    rw [word, List.length_append]
    have h := word_covers_index n
    have hp := word_length_pos n
    omega

/-- The infinite ternary word, the limit of the nested positive stages. -/
def infiniteWord : Nat → Option Fibonacci.Letter :=
  prefixLimit (fun n => word (n + 1)) word_covers_index

theorem factor_infiniteWord_iff (v : List (Option Fibonacci.Letter)) :
    (∃ i : Nat, v = List.ofFn (fun j : Fin v.length => infiniteWord (i + j.val))) ↔
      ∃ n : Nat, v <:+: word n := by
  have h := factor_prefixLimit_iff (fun n => word (n + 1)) word_covers_index
    (fun n => word_prefix_succ (n + 1) (Nat.succ_pos n)) v
  change (_ ↔ ∃ n, v <:+: word (n + 1)) at h
  rw [show (∃ i : Nat, v = List.ofFn (fun j : Fin v.length => infiniteWord (i + j.val))) ↔
      ∃ n, v <:+: word (n + 1) from h]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      have he : word 0 <:+: word 2 := ⟨word 1, [], by simp [word]⟩
      exact ⟨1, hn.trans he⟩
    | succ n => exact ⟨n, hn⟩

/-- Every finite factor of the infinite word y is rich, as in thm:Yrich. -/
theorem rich_factor_infiniteWord (v : List (Option Fibonacci.Letter))
    (hv : ∃ i : Nat, v = List.ofFn (fun j : Fin v.length => infiniteWord (i + j.val))) :
    Rich v :=
  rich_factor_of_fibonacci Fibonacci.rich_word v ((factor_infiniteWord_iff v).1 hv)

end Thesis.TernaryWord
