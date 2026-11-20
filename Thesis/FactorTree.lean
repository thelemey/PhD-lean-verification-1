import Std.Tactic

namespace Thesis.FactorTree

/-- For a characteristic Sturmian word this is its right-special factor
at length `k`, by the classical reversal property cited in the thesis. -/
def reversedPrefix (w : Nat → α) (k : Nat) : List α :=
  ((List.range k).map w).reverse

private theorem reversedPrefix_succ (w : Nat → α) (k : Nat) :
    reversedPrefix w (k + 1) = w k :: reversedPrefix w k := by
  simp [reversedPrefix, List.range_succ]

private theorem mem_reversedPrefix (w : Nat → α) {k : Nat} {x : α} :
    x ∈ reversedPrefix w k ↔ ∃ i < k, w i = x := by
  simp [reversedPrefix]

private theorem cons_eq_append_singleton_iff (xs : List α) (a b : α) :
    a :: xs = xs ++ [b] ↔ a = b ∧ ∀ x ∈ xs, x = a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.cons.injEq, List.mem_cons]
    constructor
    · rintro ⟨rfl, h⟩
      obtain ⟨hb, hxs⟩ := ih.mp h
      refine ⟨hb, ?_⟩
      intro y hy
      exact hy.elim id (hxs y)
    · rintro ⟨hb, h⟩
      have hx := h x (.inl rfl)
      subst x
      exact ⟨rfl, ih.mpr ⟨hb, fun y hy => h y (.inr hy)⟩⟩

/-- The two reversed prefixes are joined by a prefix-tree edge exactly
when the longer prefix is still inside the initial constant run.
Consequently, once the reversal property is supplied for a characteristic
Sturmian word, this proves the special-to-special adjacency step of
`thm:factortree`. -/
theorem reversedPrefixes_adjacent_iff (w : Nat → α) {d : Nat} (hd : 0 < d)
    (x : α) (hrun : ∀ i < d, w i = x) (hchange : w d ≠ x) (k : Nat) :
    (∃ a, reversedPrefix w (k + 1) = reversedPrefix w k ++ [a]) ↔ k < d := by
  rw [reversedPrefix_succ]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨_, hw⟩ := (cons_eq_append_singleton_iff _ _ _).1 ha
    by_cases h : k < d
    · exact h
    · have hzero : w 0 = w k := hw _ ((mem_reversedPrefix w).2 ⟨0, by omega, rfl⟩)
      have hk : w k = x := hzero.symm.trans (hrun 0 hd)
      have hdk : w d = w k := by
        by_cases he : d = k
        · rw [he]
        · exact hw _ ((mem_reversedPrefix w).2 ⟨d, by omega, rfl⟩)
      exact False.elim (hchange (hdk.trans hk))
  · intro hk
    refine ⟨w k, (cons_eq_append_singleton_iff _ _ _).2 ⟨rfl, ?_⟩⟩
    intro y hy
    obtain ⟨i, hi, rfl⟩ := (mem_reversedPrefix w).1 hy
    exact (hrun i (by omega)).trans (hrun k hk).symm

/-- Counts of undirected edges grouped by the two endpoint degrees.
These are the only degree pairs in the truncated Sturmian factor tree. -/
structure EdgeCounts where
  oneTwo : Int
  oneThree : Int
  twoTwo : Int
  twoThree : Int
  threeThree : Int

def EdgeCounts.total (e : EdgeCounts) : Int :=
  e.oneTwo + e.oneThree + e.twoTwo + e.twoThree + e.threeThree

def EdgeCounts.albertson (e : EdgeCounts) : Int :=
  e.oneTwo + 2 * e.oneThree + e.twoThree

def EdgeCounts.quadraticAlbertson (e : EdgeCounts) : Int :=
  3 * e.oneTwo + 8 * e.oneThree + 5 * e.twoThree

def EdgeCounts.secondZagreb (e : EdgeCounts) : Int :=
  2 * e.oneTwo + 3 * e.oneThree + 4 * e.twoTwo + 6 * e.twoThree + 9 * e.threeThree

/-- Converts the degree counts in the proof of `thm:factortree` to the
four indices. The hypotheses say which counts must still be obtained
from the Sturmian language and tree structure. The total counts are
doubled to avoid integer division. -/
theorem indices_of_counts (n d v₂ : Int) (e : EdgeCounts)
    (hv : 2 * (v₂ + (n - 1) + (n + 1)) = (n + 1) * (n + 2))
    (he : 2 * e.total = (n + 1) * (n + 2) - 2)
    (h12 : e.oneTwo = n - 1) (h13 : e.oneThree = 2)
    (h23 : e.twoThree = 3 * n - 3 - 2 * d) (h33 : e.threeThree = d - 1) :
    e.albertson = 4 * n - 2 * d ∧
    e.quadraticAlbertson = 18 * n - 10 * d - 2 ∧
    (n + 1) + 4 * v₂ + 9 * (n - 1) = 2 * (n * n) + 8 * n - 4 ∧
    e.secondZagreb = 2 * (n * n) + 10 * n - 11 + d := by
  have hpoly : (n + 1) * (n + 2) = n * n + 3 * n + 2 := by
    simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_comm n 2]
    omega
  rw [hpoly] at hv he
  unfold EdgeCounts.total at he
  unfold EdgeCounts.albertson EdgeCounts.quadraticAlbertson EdgeCounts.secondZagreb
  omega

end Thesis.FactorTree
