import Thesis.PalindromeFactors
import Thesis.Palindrome
import Mathlib.Data.List.OfFn

namespace Thesis.PalindromeFactors

variable {α : Type*}

/-- The finite word of length n starting at position i. -/
def factorList (w : Nat → α) (i n : Nat) : List α := List.ofFn fun j : Fin n => w (i+j.val)

theorem factorList_succ (w : Nat → α) (i n : Nat) :
    factorList w i (n+1) = factorList w i n ++ [w (i+n)] := by
  simpa [factorList, List.concat_eq_append] using
    (List.ofFn_succ' (fun j : Fin (n+1) => w (i+j.val)))

theorem factorList_add (w : Nat → α) (i n k : Nat) :
    factorList w i (n+k) = factorList w i n ++ factorList w (i+n) k := by
  induction k with
  | zero => simp [factorList]
  | succ k ih =>
    rw [← Nat.add_assoc, factorList_succ, ih, factorList_succ, List.append_assoc, Nat.add_assoc]

theorem factorList_prefix (w : Nat → α) {m n : Nat} (hm : m ≤ n) :
    factorList w 0 m <+: factorList w 0 n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact ⟨_, (factorList_add ..).symm⟩

/-- The source calls an infinite word rich when each finite factor is rich. -/
def InfiniteRich (w : Nat → α) : Prop := ∀ i n, Rich (factorList w i n)

theorem infiniteRich_iff_prefixes (w : Nat → α) :
    InfiniteRich w ↔ ∀ n, Rich (factorList w 0 n) := by
  refine ⟨fun h n => h 0 n, ?_⟩
  intro h i n
  apply rich_of_infix (h (i+n))
  refine ⟨factorList w 0 i, [], ?_⟩
  simp [factorList_add]

theorem framed_prefix_eq (w : Nat → α) (n : Nat) :
    framed (factorList w 0 n) = factorList (insertSeparator w) 0 (2*n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : 2*(n+1)+1 = (2*n+1)+1+1 := by omega
    rw [he, factorList_succ (insertSeparator w) 0 (2*n+1+1),
      factorList_succ (insertSeparator w) 0 (2*n+1), ← ih, factorList_succ w]
    simp [framed, interleave_append, interleave, insertSeparator, List.append_assoc,
      show (2*n+1+1)%2=0 by omega, show (2*n+1)/2=n by omega]

/-- The corollary after thm:Yrich: inserting the fresh separator in any rich
infinite word preserves richness. The converse follows from the same finite
framing equivalence in lem:insertcount. -/
theorem infiniteRich_insertSeparator_iff (w : Nat → α) :
    InfiniteRich (insertSeparator w) ↔ InfiniteRich w := by
  rw [infiniteRich_iff_prefixes, infiniteRich_iff_prefixes]
  constructor
  · intro h n
    apply (rich_framed_iff _).1
    rw [framed_prefix_eq]
    exact h _
  · intro h n
    have hf := (rich_framed_iff _).2 (h n)
    rw [framed_prefix_eq] at hf
    exact rich_of_infix hf (factorList_prefix _ (by omega)).isInfix

end Thesis.PalindromeFactors
