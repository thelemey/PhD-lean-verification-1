import Thesis.EpisturmianRecurrence
import Thesis.MBonacciWordDensity

namespace Thesis.MBonacci

/-- The repeated directive a₁ … aₘ, with m = n + 2. -/
def cyclicDirective (n i : Nat) : Fin (n + 2) :=
  ⟨directive (n + 2) i, Nat.mod_lt _ (by omega)⟩

/-- The m-bonacci word as the standard episturmian word of its directive. -/
noncomputable def standardWord (n : Nat) : Nat → Fin (n + 2) :=
  Episturmian.word (cyclicDirective n)

noncomputable def palindromePrefixLengths (n i : Nat) : Nat :=
  (Episturmian.stage (cyclicDirective n) i).length

theorem palindromePrefixLengths_strictMono (n : Nat) :
    StrictMono (palindromePrefixLengths n) :=
  Episturmian.stage_length_strictMono _

theorem standardWord_palPrefix_iff (n k : Nat) :
    PalPrefix (standardWord n) k ↔ ∃ i, palindromePrefixLengths n i = k :=
  Episturmian.palPrefix_word_iff _ _

/-- During the first cycle every directive letter is new. -/
theorem palindromePrefixLengths_firstCycle (n i : Nat) (hi : i ≤ n + 2) :
    palindromePrefixLengths n i = 2 ^ i - 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hnew : ∀ j < i, cyclicDirective n j ≠ cyclicDirective n i := fun j hj h =>
      directive_first_occurrence (show i < n + 2 by omega) j hj (congrArg Fin.val h)
    have hh := Episturmian.stage_length_of_new_letter (cyclicDirective n) i hnew
    change palindromePrefixLengths n (i + 1) = 2 * palindromePrefixLengths n i + 1 at hh
    change palindromePrefixLengths n (i + 1) = 2 ^ (i + 1) - 1
    rw [hh, ih (by omega), pow_succ]
    have hp : 0 < (2 : Nat) ^ i := Nat.pow_pos (by decide)
    omega

/-- The previous occurrence is one complete cycle back, so the
palindrome lengths satisfy the recurrence used in prop:mbonacci. -/
theorem palindromePrefixLengths_step (n i : Nat) (hi : n + 2 ≤ i) :
    palindromePrefixLengths n (i + 1) =
      2 * palindromePrefixLengths n i - palindromePrefixLengths n (i - (n + 2)) := by
  obtain ⟨h₁, h₂, h₃⟩ := directive_previous_occurrence (show 0 < n + 2 by omega) hi
  exact Episturmian.stage_length_of_previous_letter (cyclicDirective n) h₁ (Fin.ext h₂)
    (fun j hj hji he => h₃ j hj hji (congrArg Fin.val he))

theorem palindromePrefixLengths_recurrence (n : Nat) :
    PrefixLengthRecurrence n (palindromePrefixLengths n) := by
  intro k hk
  let m := n + 2
  have he := palindromePrefixLengths_step n (k + m) (by dsimp [m]; omega)
  change palindromePrefixLengths n (k + m + 1) =
    2 * palindromePrefixLengths n (k + m) - palindromePrefixLengths n (k + m - m) at he
  rw [Nat.add_sub_cancel] at he
  have hmono := (palindromePrefixLengths_strictMono n).monotone (Nat.le_add_right k m)
  have hbound : palindromePrefixLengths n k ≤ 2 * palindromePrefixLengths n (k + m) := by
    change palindromePrefixLengths n k ≤ palindromePrefixLengths n (k + m) at hmono
    omega
  have hcast := congrArg (fun j : Nat => (j : ℝ)) he
  simpa only [Nat.cast_sub hbound, Nat.cast_mul, Nat.cast_ofNat] using hcast

/-- The claimed density 1/βₘ for the actual m-bonacci word, expressed
by its strict rational lower cut. -/
theorem standardWord_below_density_iff (n : Nat) {p q : Nat} (hq : 0 < q) :
    BelowPalDensity (standardWord n) p q ↔ (p : ℝ) / q < 1 / beta n :=
  below_density_of_prefix_recurrence n _ (palindromePrefixLengths n)
    (palindromePrefixLengths_strictMono n) (standardWord_palPrefix_iff n)
    (palindromePrefixLengths_recurrence n) hq

end Thesis.MBonacci
