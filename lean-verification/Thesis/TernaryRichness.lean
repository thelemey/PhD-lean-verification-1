import Thesis.FibonacciMechanical
import Thesis.SturmianFactorRichness
import Thesis.FibonacciCentralPrefixes
import Thesis.TernaryWord
import Thesis.WordPrefixLimits

namespace Thesis.TernaryWord

open PalindromeFactors WordPrefixLimits

/-- The proof of thm:Yrich invokes the general Sturmian richness theorem
for a Fibonacci prefix, with its two symbols renamed. -/
theorem rich_fibonacci_prefix (n : Nat) : Rich (Fibonacci.word n) := by
  let e : Bool ≃ Fibonacci.Letter :=
    ⟨fun b => if b then .b else .a, fun x => match x with | .a => false | .b => true,
      fun b => by cases b <;> rfl, fun x => by cases x <;> rfl⟩
  have h := FactorTree.characteristicWord_infiniteRich Fibonacci.mechanicalSlope_pos
    Fibonacci.mechanicalSlope_lt_one Fibonacci.mechanicalSlope_irrational 0 (Fibonacci.word n).length
  have he : (factorList (FactorTree.characteristicWord Fibonacci.mechanicalSlope) 0
      (Fibonacci.word n).length).map e = Fibonacci.word n := by
    conv_rhs => rw [Fibonacci.word_eq_mechanical_prefix n]
    apply List.ext_getElem (by simp [factorList])
    intro j _ _
    simp only [List.getElem_map, factorList, List.getElem_ofFn, Nat.zero_add]
    rfl
  exact he ▸ rich_rename e h

/-- The finite assertion of thm:Yrich, via its original separator proof. -/
theorem rich_word (n : Nat) : Rich (word n) :=
  rich_word_of_fibonacci rich_fibonacci_prefix n

theorem palindromic_factor_count (n : Nat) :
    ∃ ps, Enumerates (word n) ps ∧ ps.length = 2 * Fibonacci.fib (n + 1) :=
  factor_count_of_fibonacci rich_fibonacci_prefix n

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

/-- The identity of infinite words in lem:Ystructure. The alphabet of
Fibonacci.infiniteWord is already renamed through the two some symbols. -/
theorem infiniteWord_eq_insertSeparator :
    infiniteWord = insertSeparator Fibonacci.infiniteWord := by
  have even (j : Nat) : infiniteWord (2 * j) = none := by
    have h := Fibonacci.word_covers j
    have he := word_succ_eq_interleave j
    have hlen : 2 * j < (word (j + 1)).length := by
      rw [he, length_interleave]
      omega
    have hh := prefixLimit_eq_getElem (fun n => word (n + 1)) word_covers_index
      (fun n => word_prefix_succ (n + 1) (Nat.succ_pos n)) hlen
    change infiniteWord (2 * j) = _ at hh
    exact hh.trans (by simpa only [he] using getElem_interleave_even (Fibonacci.word j) j h)
  have odd (j : Nat) : infiniteWord (2 * j + 1) = some (Fibonacci.infiniteWord j) := by
    have h := Fibonacci.word_covers j
    have he := word_succ_eq_interleave j
    have hlen : 2 * j + 1 < (word (j + 1)).length := by
      rw [he, length_interleave]
      omega
    have hh := prefixLimit_eq_getElem (fun n => word (n + 1)) word_covers_index
      (fun n => word_prefix_succ (n + 1) (Nat.succ_pos n)) hlen
    change infiniteWord (2 * j + 1) = _ at hh
    exact hh.trans (by simpa only [he] using getElem_interleave_odd (Fibonacci.word j) j h)
  funext i
  by_cases h : i % 2 = 0
  · rw [show i = 2 * (i / 2) by omega, even]
    simp [insertSeparator]
  · rw [show i = 2 * (i / 2) + 1 by omega, odd]
    simp [insertSeparator]
    congr 1
    omega

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
  rich_factor_of_fibonacci rich_fibonacci_prefix v ((factor_infiniteWord_iff v).1 hv)

end Thesis.TernaryWord
