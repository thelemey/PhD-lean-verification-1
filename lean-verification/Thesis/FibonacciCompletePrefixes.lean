import Thesis.FibonacciCentralPrefixes
import Thesis.MBonacciClosureDensity
import Thesis.FibonacciTableLimit

namespace Thesis.Fibonacci

theorem fib_at_least_two (n : Nat) : 2 ≤ fib (n + 3) := by
  change 2 ≤ fib (n + 1) + fib (n + 2)
  have := fib_positive n
  have : 0 < fib (n + 2) := fib_positive (n + 1)
  omega

theorem binary_closure_lengths (n : Nat) :
    MBonacci.palindromePrefixLengths 0 n = (central n).length := by
  rw [central_length]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · simpa using MBonacci.palindromePrefixLengths_firstCycle 0 0 (by decide)
    · simpa using MBonacci.palindromePrefixLengths_firstCycle 0 1 (by decide)
    · simpa using MBonacci.palindromePrefixLengths_firstCycle 0 2 (by decide)
    have he := MBonacci.palindromePrefixLengths_step 0 (n + 2) (by omega)
    simp only [Nat.zero_add, Nat.add_sub_cancel] at he
    rw [he, ih (n + 2) (by omega), ih n (by omega)]
    have h1 : fib (n + 5) = fib (n + 3) + fib (n + 4) := rfl
    have h2 : fib (n + 6) = fib (n + 4) + fib (n + 5) := rfl
    change 2 * (fib (n + 5) - 2) - (fib (n + 3) - 2) = fib (n + 6) - 2
    have ha := fib_at_least_two n
    have hb := fib_at_least_two (n + 2)
    omega

private theorem central_next_length_le (n : Nat) :
    (central (n + 1)).length ≤ 2 * ((central n).length + 1) := by
  rw [central_length, central_length]
  have h1 : fib (n + 3) = fib (n + 1) + fib (n + 2) := rfl
  have h2 : fib (n + 4) = fib (n + 2) + fib (n + 3) := rfl
  have h := fib_at_least_two n
  change fib (n + 4) - 2 ≤ 2 * (fib (n + 3) - 2 + 1)
  omega

/-- Match the binary closure alphabet to the two letters of the finite recursion. -/
def binaryLetter (i : Fin 2) : Letter := if i.val = 0 then .a else .b

private theorem binaryLetter_injective : Function.Injective binaryLetter := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  by_cases hz : i.val = 0 <;> by_cases hz' : j.val = 0 <;>
    simp [binaryLetter, hz, hz'] at h <;> omega

private theorem map_binary_palPrefix_iff (w : Nat → Fin 2) (L : Nat) :
    PalPrefix (fun i => binaryLetter (w i)) L ↔ PalPrefix w L :=
  ⟨fun h i hi => binaryLetter_injective (h i hi), fun h i hi => congrArg binaryLetter (h i hi)⟩

/-- The standard binary episturmian word is the recurrence word. At each
stage the previous common prefix plus its next letter determines the
whole palindrome, since the known stage length is at most twice that size. -/
theorem infiniteWord_eq_binary_closure :
    infiniteWord = fun i => binaryLetter (MBonacci.standardWord 0 i) := by
  let g := fun i => binaryLetter (MBonacci.standardWord 0 i)
  have pals (n : Nat) : PalPrefix infiniteWord (central n).length ∧
      PalPrefix g (central n).length := by
    constructor
    · rw [central_length]
      exact central_palPrefix n
    · apply (map_binary_palPrefix_iff _ _).2
      exact (MBonacci.standardWord_palPrefix_iff 0 _).2 ⟨n, binary_closure_lengths n⟩
  have next (n : Nat) : infiniteWord (central n).length = g (central n).length := by
    have he := Episturmian.word_at_stage_length (MBonacci.cyclicDirective 0) n
    change MBonacci.standardWord 0 (MBonacci.palindromePrefixLengths 0 n) =
      MBonacci.cyclicDirective 0 n at he
    rw [binary_closure_lengths] at he
    rw [infiniteWord_after_central]
    change (if n % 2 = 0 then Letter.a else Letter.b) =
      binaryLetter (MBonacci.standardWord 0 (central n).length)
    rw [he]
    rfl
  have agree (n : Nat) : ∀ i < (central n).length, infiniteWord i = g i := by
    induction n with
    | zero => simp [central]
    | succ n ih =>
      intro i hi
      have hbound := central_next_length_le n
      have small (j : Nat) (hj : j ≤ (central n).length) : infiniteWord j = g j := by
        rcases lt_or_eq_of_le hj with h | rfl
        · exact ih j h
        · exact next n
      by_cases h : i ≤ (central n).length
      · exact small i h
      · have hj : (central (n + 1)).length - 1 - i ≤ (central n).length := by omega
        exact ((pals (n + 1)).1 i hi).trans
          ((small _ hj).trans ((pals (n + 1)).2 i hi).symm)
  funext i
  have hlarge : i < (central (i + 1)).length := by
    rw [← binary_closure_lengths]
    exact (Nat.lt_succ_self i).trans_le (Episturmian.stage_length_ge _ _)
  exact agree _ _ hlarge

/-- The full list of palindrome-prefix lengths cited after lem:palFib. -/
theorem infiniteWord_palPrefix_iff (L : Nat) :
    PalPrefix infiniteWord L ↔ ∃ n, fib (n + 3) - 2 = L := by
  rw [infiniteWord_eq_binary_closure, map_binary_palPrefix_iff, MBonacci.standardWord_palPrefix_iff]
  simp only [binary_closure_lengths, central_length]

end Thesis.Fibonacci
