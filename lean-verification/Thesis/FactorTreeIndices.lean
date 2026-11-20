import Thesis.FactorTreeMixedEdges

open scoped BigOperators
open Thesis.ThueMorse (complexity)

namespace Thesis.FactorTree

/-- Albertson's index is the sum of the absolute differences of the
endpoint degrees. -/
noncomputable def albertsonOfWord (w : Nat → Bool) (n : Nat) : ℤ :=
  ∑ e ∈ factorEdges w n,
    |((edgeDegrees w n e).1 : ℤ) - ((edgeDegrees w n e).2 : ℤ)|

/-- The quadratic Albertson index uses the difference of squared degrees. -/
noncomputable def quadraticAlbertsonOfWord (w : Nat → Bool) (n : Nat) : ℤ :=
  ∑ e ∈ factorEdges w n,
    |((edgeDegrees w n e).1 : ℤ) ^ 2 - ((edgeDegrees w n e).2 : ℤ) ^ 2|

/-- The second Zagreb index is the sum of endpoint degree products. -/
noncomputable def secondZagrebOfWord (w : Nat → Bool) (n : Nat) : ℤ :=
  ∑ e ∈ factorEdges w n, ((edgeDegrees w n e).1 : ℤ) * ((edgeDegrees w n e).2 : ℤ)

private theorem edge_indices_by_counts (w : Nat → Bool) (n : Nat)
    (hwidth : ∀ j, complexity w j = j + 1) :
    albertsonOfWord w n = (factorEdgeCounts w n).albertson ∧
    quadraticAlbertsonOfWord w n = (factorEdgeCounts w n).quadraticAlbertson ∧
    secondZagrebOfWord w n = (factorEdgeCounts w n).secondZagreb := by
  have h₁ := sum_edgeDegrees_eq w n hwidth (fun (p, c) => |(p : ℤ) - (c : ℤ)|)
  have h₂ := sum_edgeDegrees_eq w n hwidth (fun (p, c) => |(p : ℤ) ^ 2 - (c : ℤ) ^ 2|)
  have h₃ := sum_edgeDegrees_eq w n hwidth (fun (p, c) => (p : ℤ) * (c : ℤ))
  change albertsonOfWord w n = _ at h₁
  change quadraticAlbertsonOfWord w n = _ at h₂
  change secondZagrebOfWord w n = _ at h₃
  norm_num [factorEdgeCounts, EdgeCounts.albertson, EdgeCounts.quadraticAlbertson,
    EdgeCounts.secondZagreb] at h₁ h₂ h₃ ⊢
  exact ⟨by omega, by omega, by omega⟩

/-- The vertex count and all four indices of the actual tree of factors
in thm:factortree. Its two cited Sturmian language properties are the
complexity and reversal hypotheses. -/
theorem factor_tree_indices_of_word (w : Nat → Bool) {d n : Nat} (hd : 0 < d) (hn : d + 2 ≤ n)
    (x : Bool) (hrun : ∀ i < d, w i = x) (hchange : w d ≠ x)
    (hwidth : ∀ j, complexity w j = j + 1)
    (hreversal : ∀ j (u : Fin j → Bool), u ∈ rightSpecials w j →
      List.ofFn u = reversedPrefix w j) :
    (factorVertices w n).card = (n + 1) * (n + 2) / 2 ∧
    albertsonOfWord w n = 4 * (n : ℤ) - 2 * d ∧
    quadraticAlbertsonOfWord w n = 18 * (n : ℤ) - 10 * d - 2 ∧
    firstZagrebOfWord w n = 2 * (n : ℤ) ^ 2 + 8 * n - 4 ∧
    secondZagrebOfWord w n = 2 * (n : ℤ) ^ 2 + 10 * n - 11 + d := by
  obtain ⟨h₁, h₂, h₃⟩ := edge_indices_by_counts w n hwidth
  obtain ⟨h21, h31, h22, h23, h33⟩ := factorEdgeCounts_eq w hd hn x hrun hchange hwidth hreversal
  have hv : 2 * (factorVertices w n).card = (n + 1) * (n + 2) := by
    exact_mod_cast (factor_tree_cardinalities w n hwidth).1
  rw [h₁, h₂, h₃]
  refine ⟨by omega, ?_, ?_, firstZagrebOfWord_eq w (by omega) hwidth, ?_⟩
  · unfold EdgeCounts.albertson
    omega
  · unfold EdgeCounts.quadraticAlbertson
    omega
  · unfold EdgeCounts.secondZagreb
    omega

end Thesis.FactorTree
