import Thesis.Fibonacci
import Thesis.PalindromicMorphismRichness

namespace Thesis.Fibonacci

open PalindromeFactors

private def exchange : Letter ≃ Letter where
  toFun
    | .a => .b
    | .b => .a
  invFun
    | .a => .b
    | .b => .a
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- The usual Fibonacci substitution a ↦ ab, b ↦ a is a letter
exchange followed by the left palindromic morphism at a. -/
def fibonacciMorphism (w : List Letter) : List Letter :=
  leftPalMorphism .a (w.map exchange)

theorem fibonacciMorphism_append (w v : List Letter) :
    fibonacciMorphism (w ++ v) = fibonacciMorphism w ++ fibonacciMorphism v := by
  simp [fibonacciMorphism, leftPalMorphism_append]

theorem word_succ_eq_morphism : ∀ n, word (n + 1) = fibonacciMorphism (word n)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    change word (n + 2) ++ word (n + 1) = fibonacciMorphism (word (n + 1) ++ word n)
    rw [fibonacciMorphism_append, ← word_succ_eq_morphism (n + 1), ← word_succ_eq_morphism n]

/-- The Droubay richness input to thm:Yrich, specialized to the
finite Fibonacci words used in the dissertation. -/
theorem rich_word (n : Nat) : Rich (word n) := by
  induction n with
  | zero =>
    refine ⟨[[Letter.a]], ⟨by simp, ?_⟩, rfl⟩
    intro v
    constructor
    · intro hv
      have he : v = [Letter.a] := by simpa using hv
      subst v
      exact ⟨by decide, ⟨[], [], rfl⟩, rfl⟩
    · rintro ⟨hne, ⟨l, r, he⟩, _⟩
      have hlen := congrArg List.length he
      change (l ++ v ++ r).length = 1 at hlen
      simp only [List.length_append] at hlen
      have hv : 0 < v.length := List.length_pos_iff.2 hne
      have hl : l = [] := List.length_eq_zero_iff.1 (by omega)
      have hr : r = [] := List.length_eq_zero_iff.1 (by omega)
      simpa [hl, hr, word] using he
  | succ n ih =>
    rw [word_succ_eq_morphism]
    exact rich_leftPalMorphism .a (rich_rename exchange ih)

theorem rich_factor (v : List Letter) (h : ∃ n, v <:+: word n) : Rich v := by
  obtain ⟨n, hv⟩ := h
  exact rich_of_infix (rich_word n) hv

end Thesis.Fibonacci
