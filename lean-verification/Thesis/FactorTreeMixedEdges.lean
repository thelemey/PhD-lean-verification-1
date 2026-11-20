import Thesis.FactorTreeEdgeCounts

open scoped BigOperators
open Thesis.ThueMorse (complexity)

namespace Thesis.FactorTree

/-- Count each edge once, ignoring which endpoint is the parent. -/
noncomputable def factorEdgeCounts (w : Nat → Bool) (n : Nat) : EdgeCounts where
  oneTwo := edgeDegreeCount w n 2 1
  oneThree := edgeDegreeCount w n 3 1
  twoTwo := edgeDegreeCount w n 2 2
  twoThree := edgeDegreeCount w n 2 3 + edgeDegreeCount w n 3 2
  threeThree := edgeDegreeCount w n 3 3

theorem factorEdgeCounts_total (w : Nat → Bool) (n : Nat)
    (hwidth : ∀ j, complexity w j = j + 1) :
    (factorEdgeCounts w n).total = ((factorEdges w n).card : ℤ) := by
  have h := sum_edgeDegrees_eq w n hwidth (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at h
  simp only [factorEdgeCounts, EdgeCounts.total]
  omega

private theorem childEnds_eq (w : Nat → Bool) (n d : Nat)
    (hwidth : ∀ j, complexity w j = j + 1) :
    (childEnds w n d : ℤ) = edgeDegreeCount w n 2 d + edgeDegreeCount w n 3 d := by
  rw [← sum_indicator_child_degree]
  simp only [edgeDegreeCount_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rcases edgeDegrees_parent_cases w hwidth he with hp | hp <;>
    rw [show edgeDegrees w n e = (_, (edgeDegrees w n e).2) from Prod.ext hp rfl] <;> simp

private theorem parentEnds_three_eq (w : Nat → Bool) (n : Nat)
    (hwidth : ∀ j, complexity w j = j + 1) :
    (parentEnds w n 3 : ℤ) =
      edgeDegreeCount w n 3 1 + edgeDegreeCount w n 3 2 + edgeDegreeCount w n 3 3 := by
  have h := sum_edgeDegrees_eq w n hwidth (fun e => if e.1 = 3 then 1 else 0)
  rw [sum_indicator_parent_degree] at h
  norm_num at h
  exact h

/-- Parts (a) and (b) of the proof count separately the mixed internal
edges entering and leaving special vertices. Parts (c) and (d) count
the two types of edges to leaves. -/
theorem factorTree_mixed_edge_counts (w : Nat → Bool) {d n : Nat} (hd : 0 < d) (hn : d + 2 ≤ n)
    (x : Bool) (hrun : ∀ i < d, w i = x) (hchange : w d ≠ x)
    (hwidth : ∀ j, complexity w j = j + 1)
    (hreversal : ∀ j (u : Fin j → Bool), u ∈ rightSpecials w j →
      List.ofFn u = reversedPrefix w j) :
    edgeDegreeCount w n 2 3 = (n : ℤ) - d ∧
    edgeDegreeCount w n 3 2 = ((d : ℤ) - 1) + 2 * ((n : ℤ) - 1 - d) ∧
    edgeDegreeCount w n 3 1 = 2 ∧
    edgeDegreeCount w n 2 1 = (n : ℤ) - 1 := by
  have h33 := edgeDegreeCount_three_three w hd hn x hrun hchange hwidth hreversal
  have h31 := edgeDegreeCount_three_one w (by omega : 2 ≤ n) hwidth
  have hIn := childEnds_eq w n 3 hwidth
  have hOut := parentEnds_three_eq w n hwidth
  have hLeaf := childEnds_eq w n 1 hwidth
  have hn' : 1 ≤ n := by omega
  rw [childEnds_three w hn' hwidth, Nat.cast_sub hn'] at hIn
  rw [parentEnds_three w hn' hwidth, Nat.cast_mul, Nat.cast_sub hn'] at hOut
  rw [leaf_incidence w hn' hwidth, Nat.cast_add] at hLeaf
  exact ⟨by omega, by omega, h31, by omega⟩

/-- The five undirected counts, expressed as in the thesis. The (2,2)
count is doubled to keep the formula in integers. -/
theorem factorEdgeCounts_eq (w : Nat → Bool) {d n : Nat} (hd : 0 < d) (hn : d + 2 ≤ n)
    (x : Bool) (hrun : ∀ i < d, w i = x) (hchange : w d ≠ x)
    (hwidth : ∀ j, complexity w j = j + 1)
    (hreversal : ∀ j (u : Fin j → Bool), u ∈ rightSpecials w j →
      List.ofFn u = reversedPrefix w j) :
    let e := factorEdgeCounts w n
    e.oneTwo = (n : ℤ) - 1 ∧ e.oneThree = 2 ∧
    2 * e.twoTwo = (n : ℤ) ^ 2 + 3 * n - 2 * (4 * n - 3 - d) ∧
    e.twoThree = 3 * (n : ℤ) - 3 - 2 * d ∧ e.threeThree = (d : ℤ) - 1 := by
  obtain ⟨h23, h32, h31, h21⟩ := factorTree_mixed_edge_counts w hd hn x hrun hchange hwidth hreversal
  have h33 := edgeDegreeCount_three_three w hd hn x hrun hchange hwidth hreversal
  have ht := (factor_tree_cardinalities w n hwidth).2
  rw [← factorEdgeCounts_total w n hwidth] at ht
  unfold EdgeCounts.total at ht
  simp only [factorEdgeCounts] at ht ⊢
  have hpoly : ((n : ℤ) + 1) * (n + 2) = (n : ℤ) ^ 2 + 3 * n + 2 := by ring
  rw [hpoly] at ht
  exact ⟨h21, h31, by omega, by omega, h33⟩

end Thesis.FactorTree
