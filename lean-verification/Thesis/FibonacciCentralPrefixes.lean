import Thesis.Fibonacci
import Thesis.WordPrefixLimits
import Thesis.Palindrome

namespace Thesis.Fibonacci

open WordPrefixLimits

/-- The final two letters of s_{n+1}, with the index starting at zero. -/
def ending : Nat → List Letter
  | 0 => [.a, .b]
  | 1 => [.b, .a]
  | n + 2 => ending n

/-- The word s_{n+1} with its final two letters removed. -/
def central : Nat → List Letter
  | 0 => []
  | 1 => [.a]
  | n + 2 => word (n + 2) ++ central n

theorem word_succ_eq_central_ending : ∀ n, word (n + 1) = central n ++ ending n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    change word (n + 2) ++ word (n + 1) = (word (n + 2) ++ central n) ++ ending n
    rw [word_succ_eq_central_ending n, List.append_assoc]

private theorem ending_length : ∀ n, (ending n).length = 2
  | 0 => rfl
  | 1 => rfl
  | n + 2 => ending_length n

private theorem ending_succ_reverse : ∀ n, (ending (n + 1)).reverse = ending n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => ending_succ_reverse n

/-- The shared prefix of the concatenations in the two possible orders,
as in the inductive claim of lem:palFib. -/
theorem central_alternate : ∀ n, central (n + 2) = word (n + 1) ++ central (n + 1)
  | 0 => rfl
  | n + 1 => by
    change (word (n + 2) ++ word (n + 1)) ++ central (n + 1) =
      word (n + 2) ++ central (n + 2)
    rw [List.append_assoc, ← central_alternate n]

/-- The two descriptions of a central word have oppositely ordered
palindromic pieces and reversed final pairs, giving the palindrome
assertion in lem:palFib. -/
theorem central_reverse : ∀ n, (central n).reverse = central n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    calc
      _ = (word (n + 2) ++ central n).reverse := rfl
      _ = (central n ++ ending n) ++ central (n + 1) := by
        conv_lhs => rw [word_succ_eq_central_ending (n + 1)]
        rw [List.reverse_append, List.reverse_append, central_reverse n,
          central_reverse (n + 1), ending_succ_reverse, List.append_assoc]
      _ = word (n + 1) ++ central (n + 1) := by
        rw [← word_succ_eq_central_ending n]
      _ = _ := (central_alternate n).symm

theorem central_length (n : Nat) : (central n).length = fib (n + 3) - 2 := by
  have h := congrArg List.length (word_succ_eq_central_ending n)
  rw [word_length, List.length_append, ending_length] at h
  change fib (n + 3) = (central n).length + 2 at h
  omega

private theorem word_prefix_step (n : Nat) : word n <+: word (n + 1) := by
  cases n with
  | zero => exact ⟨[.b], rfl⟩
  | succ n => exact List.prefix_append _ _

private theorem word_length_pos : ∀ n, 0 < (word n).length
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    rw [word, List.length_append]
    exact Nat.add_pos_left (word_length_pos (n + 1)) _

theorem word_covers : ∀ n, n < (word n).length
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    rw [word, List.length_append]
    have ha := word_covers (n + 1)
    have hb := word_length_pos n
    omega

/-- The infinite Fibonacci word in its finite-word recurrence representation. -/
def infiniteWord : Nat → Letter := prefixLimit word word_covers

theorem central_palPrefix (n : Nat) : PalPrefix infiniteWord (fib (n + 3) - 2) := by
  rw [← central_length n]
  intro i hi
  have hj : (central n).length - 1 - i < (central n).length := by omega
  have hpre : central n <+: word (n + 1) := ⟨ending n, (word_succ_eq_central_ending n).symm⟩
  have h₁ := prefixLimit_eq_getElem word word_covers word_prefix_step (hi.trans_le hpre.length_le)
  have h₂ := prefixLimit_eq_getElem word word_covers word_prefix_step (hj.trans_le hpre.length_le)
  change prefixLimit word word_covers i =
    prefixLimit word word_covers ((central n).length - 1 - i)
  rw [h₁, h₂, ← hpre.getElem hi, ← hpre.getElem hj]
  have he := congrArg (fun v : List Letter => v[i]?) (central_reverse n)
  have hir : i < (central n).reverse.length := by simpa using hi
  have hh : (central n)[(central n).length - 1 - i] = (central n)[i] := by
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hir,
      List.getElem_reverse, Option.some.injEq] using he
  exact hh.symm

/-- The letter following the central prefix is the first of its alternating ending. -/
theorem infiniteWord_after_central (n : Nat) :
    infiniteWord (central n).length = if n % 2 = 0 then .a else .b := by
  have hlen : (central n).length < (word (n + 1)).length := by
    rw [word_succ_eq_central_ending, List.length_append, ending_length]
    omega
  have hread := prefixLimit_eq_getElem word word_covers word_prefix_step hlen
  change infiniteWord (central n).length = _ at hread
  have he := congrArg (fun w : List Letter => w[(central n).length]?)
    (word_succ_eq_central_ending n)
  dsimp only at he
  rw [List.getElem?_eq_getElem hlen, List.getElem?_append_right (le_refl _),
    Nat.sub_self, ← List.head?_eq_getElem?] at he
  have hhead (k : Nat) : (ending k).head? = some (if k % 2 = 0 then Letter.a else Letter.b) := by
    induction k using Nat.twoStepInduction with
    | zero => rfl
    | one => rfl
    | more k ih _ =>
      have hmod : (k + 2) % 2 = k % 2 := by omega
      simpa only [ending, hmod] using ih
  exact hread.trans (Option.some.inj (he.trans (hhead n)))


end Thesis.Fibonacci
