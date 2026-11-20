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

/-- Count the edges between the distinguished prefixes at internal levels.
The lower endpoint is at one of the levels `1, …, n - 2`: the root and
the leaves do not have degree three. -/
theorem count_adjacent_reversedPrefixes (w : Nat → α) {d n : Nat}
    (hd : 0 < d) (hn : d + 2 ≤ n) (x : α)
    (hrun : ∀ i < d, w i = x) (hchange : w d ≠ x)
    (adjacent : Nat → Bool)
    (hedge : ∀ k, 1 ≤ k → k ≤ n - 2 →
      (adjacent k = true ↔ ∃ a, reversedPrefix w (k + 1) = reversedPrefix w k ++ [a])) :
    (List.range' 1 (n - 2)).countP adjacent = d - 1 := by
  have htest : ∀ k ∈ List.range' 1 (n - 2),
      adjacent k = true ↔ decide (k < d) = true := by
    intro k hk
    have hk' := List.mem_range'_1.mp hk
    rw [hedge k hk'.1 (by omega), reversedPrefixes_adjacent_iff w hd x hrun hchange,
      decide_eq_true_eq]
  rw [List.countP_congr htest]
  have hsplit : List.range' 1 (n - 2) =
      List.range' 1 (d - 1) ++ List.range' d (n - d - 1) := by
    have hs := List.range'_append_1 (s := 1) (m := d - 1) (n := n - d - 1)
    simpa only [show 1 + (d - 1) = d by omega,
      show d - 1 + (n - d - 1) = n - 2 by omega] using hs.symm
  rw [hsplit, List.countP_append]
  have hfirst : (List.range' 1 (d - 1)).countP (fun k => decide (k < d)) = d - 1 := by
    calc
      _ = (List.range' 1 (d - 1)).length := by
        apply List.countP_eq_length.mpr
        intro k hk
        have hk' := List.mem_range'_1.mp hk
        exact decide_eq_true (by omega)
      _ = d - 1 := List.length_range'
  have hlast : (List.range' d (n - d - 1)).countP (fun k => decide (k < d)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro k hk
    simp only [decide_eq_true_eq]
    exact Nat.not_lt_of_ge (List.mem_range'_1.mp hk).1
  simp [hfirst, hlast]

def vertexCount (width : Nat → Int) (n : Nat) : Int :=
  ((List.range (n + 1)).map width).sum

/-- Each vertex at a positive level contributes its one edge to its parent. -/
def parentEdgeCount (width : Nat → Int) (n : Nat) : Int :=
  ((List.range n).map fun k => width (k + 1)).sum

private theorem sum_append_singleton (xs : List Int) (x : Int) :
    (xs ++ [x]).sum = xs.sum + x := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih, Int.add_assoc]

private theorem twice_sum_width (n : Nat) :
    2 * vertexCount (fun k => (k : Int) + 1) n = ((n : Int) + 1) * (n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 * (((List.range (n + 2)).map fun (k : Nat) => (k : Int) + 1).sum) = _
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, sum_append_singleton]
    change 2 * (vertexCount (fun k => (k : Int) + 1) n + (((n + 1 : Nat) : Int) + 1)) = _
    simp only [Int.ofNat_succ]
    have hp : ((n : Int) + 1 + 1) * ((n : Int) + 1 + 2) =
        ((n : Int) + 1) * ((n : Int) + 2) + 2 * ((n : Int) + 2) := by
      simp only [Int.add_mul, Int.mul_add, Int.one_mul]
      omega
    rw [hp]
    omega

/-- Vertex and edge totals from the Sturmian factor complexity `k + 1`. -/
theorem counts_of_level_width (width : Nat → Int) (n : Nat)
    (hwidth : ∀ k ≤ n, width k = (k : Int) + 1) :
    2 * vertexCount width n = ((n : Int) + 1) * (n + 2) ∧
    2 * parentEdgeCount width n = ((n : Int) + 1) * (n + 2) - 2 := by
  have hvertices : 2 * vertexCount width n = ((n : Int) + 1) * (n + 2) := by
    unfold vertexCount
    rw [List.map_congr_left (l := List.range (n + 1))
      (g := fun k : Nat => (k : Int) + 1)
      (fun k hk => hwidth k (by have := List.mem_range.mp hk; omega))]
    exact twice_sum_width n
  have hzero := hwidth 0 (by omega)
  have he : vertexCount width n = width 0 + parentEdgeCount width n := by
    unfold vertexCount parentEdgeCount
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      Function.comp_def, Nat.succ_eq_add_one]
  exact ⟨hvertices, by omega⟩

/-- The degree-three incidence count includes two ends of each `(3,3)` edge. -/
def EdgeCounts.degreeThreeEnds (e : EdgeCounts) : Int :=
  e.oneThree + e.twoThree + 2 * e.threeThree

/-- Recover the two mixed edge counts by counting leaf and degree-three
incidences. The only individually supplied edge counts are the two edges
from the last internal special factor to leaves, and the special-to-special edges. -/
theorem mixed_edges_of_incidence (n d : Int) (e : EdgeCounts)
    (hleaves : e.oneTwo + e.oneThree = n + 1)
    (hdegreeThree : e.degreeThreeEnds = 3 * (n - 1))
    (h13 : e.oneThree = 2) (h33 : e.threeThree = d - 1) :
    e.oneTwo = n - 1 ∧ e.twoThree = 3 * n - 3 - 2 * d := by
  unfold EdgeCounts.degreeThreeEnds at hdegreeThree
  omega

/-- The first Zagreb index for a tree with degrees one, two and three. -/
def firstZagreb (leaves degreeTwo degreeThree : Int) : Int :=
  leaves + 4 * degreeTwo + 9 * degreeThree

/-- The factor-tree formulas from the level sizes, the prefix description
of the special factors, and the degree-incidence data. In particular, the
counts of the `(1,2)`, `(2,3)`, and `(3,3)` edges are conclusions of
the counting argument, not assumed numerical formulas. -/
theorem factor_tree_indices_of_structure (w : Nat → α) {d n : Nat}
    (hd : 0 < d) (hn : d + 2 ≤ n) (x : α)
    (hrun : ∀ i < d, w i = x) (hchange : w d ≠ x)
    (width : Nat → Int) (hwidth : ∀ k ≤ n, width k = (k : Int) + 1)
    (adjacent : Nat → Bool)
    (hedge : ∀ k, 1 ≤ k → k ≤ n - 2 →
      (adjacent k = true ↔ ∃ a, reversedPrefix w (k + 1) = reversedPrefix w k ++ [a]))
    (v₂ : Int) (e : EdgeCounts)
    (hvertices : v₂ + ((n : Int) - 1) + width n = vertexCount width n)
    (hedges : e.total = parentEdgeCount width n)
    (hleaves : e.oneTwo + e.oneThree = width n)
    (hdegreeThree : e.degreeThreeEnds = 3 * ((n : Int) - 1))
    (hlastSpecial : e.oneThree = 2)
    (hspecialEdges : e.threeThree = ((List.range' 1 (n - 2)).countP adjacent : Int)) :
    2 * vertexCount width n = ((n : Int) + 1) * (n + 2) ∧
    e.albertson = 4 * (n : Int) - 2 * d ∧
    e.quadraticAlbertson = 18 * (n : Int) - 10 * d - 2 ∧
    firstZagreb (width n) v₂ ((n : Int) - 1) = 2 * ((n : Int) * n) + 8 * n - 4 ∧
    e.secondZagreb = 2 * ((n : Int) * n) + 10 * n - 11 + d := by
  have h33 : e.threeThree = (d : Int) - 1 := by
    rw [hspecialEdges, count_adjacent_reversedPrefixes w hd hn x hrun hchange adjacent hedge]
    omega
  have hwidthn := hwidth n (Nat.le_refl _)
  rw [hwidthn] at hvertices hleaves
  have ⟨hvertexTotal, hedgeTotal⟩ := counts_of_level_width width n hwidth
  have ⟨h12, h23⟩ := mixed_edges_of_incidence n d e hleaves hdegreeThree hlastSpecial h33
  refine ⟨hvertexTotal, ?_⟩
  rw [hwidthn]
  exact indices_of_counts n d v₂ e (by rw [hvertices]; exact hvertexTotal)
    (by rw [hedges]; exact hedgeTotal) h12 hlastSpecial h23 h33

end Thesis.FactorTree
