import Thesis.FactorTreeIndices

open Thesis.ThueMorse (complexity)

namespace Thesis.FactorTree

/-- Each row gives d, the vertex count, the two Albertson indices,
and the two Zagreb indices, in that order. -/
def depthEightTable : List (Nat × Nat × ℤ × ℤ × ℤ × ℤ) :=
  [(1, 45, 30, 132, 188, 198), (2, 45, 28, 122, 188, 199),
    (3, 45, 26, 112, 188, 200), (4, 45, 24, 102, 188, 201)]

/-- Check all four rows of the depth-eight table following thm:factortree
using the formulas for the vertex and edge sums. -/
theorem depth_eight_table_row (w : Nat → Bool) {d : Nat} (hd : 0 < d) (hd' : d ≤ 4)
    (x : Bool) (hrun : ∀ i < d, w i = x) (hchange : w d ≠ x)
    (hwidth : ∀ j, complexity w j = j + 1)
    (hreversal : ∀ j (u : Fin j → Bool), u ∈ rightSpecials w j →
      List.ofFn u = reversedPrefix w j) :
    (d, (factorVertices w 8).card, albertsonOfWord w 8, quadraticAlbertsonOfWord w 8,
      firstZagrebOfWord w 8, secondZagrebOfWord w 8) ∈ depthEightTable := by
  obtain ⟨hv, ha, hq, h₁, h₂⟩ :=
    factor_tree_indices_of_word w (n := 8) hd (by omega) x hrun hchange hwidth hreversal
  rw [hv, ha, hq, h₁, h₂]
  interval_cases d <;> decide

end Thesis.FactorTree
