import Thesis.SturmianMechanical
import Thesis.FactorTreeIndices
import Thesis.FactorTreeTable

open Thesis.ThueMorse (complexity complexity_ge_of_not_eventually_periodic)

namespace Thesis.FactorTree

/-- Property (F1) for the mechanically defined characteristic word.
Property (F2) gives at most one right-special factor at each level, and
aperiodicity gives the matching Morse–Hedlund lower bound. -/
theorem characteristic_complexity (a : ℝ) (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) (k : Nat) :
    complexity (characteristicWord a) k = k + 1 := by
  have hcard (j : Nat) : (rightSpecials (characteristicWord a) j).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro u hu v hv
    exact List.ofFn_inj.1 ((characteristic_rightSpecial_eq_reversedPrefix ha ha' hirr j u hu).trans
      (characteristic_rightSpecial_eq_reversedPrefix ha ha' hirr j v hv).symm)
  have hupper (j : Nat) : complexity (characteristicWord a) j ≤ j + 1 := by
    induction j with
    | zero => exact Finset.card_le_one.2 (fun _ _ _ _ => Subsingleton.elim _ _)
    | succ j ih =>
      rw [complexity_succ_eq_add_rightSpecials]
      have := hcard j
      omega
  exact le_antisymm (hupper k) (complexity_ge_of_not_eventually_periodic _
    (characteristic_not_eventually_periodic ha ha' hirr) k)

/-- Theorem thm:factortree for the characteristic word of an irrational
slope, with the two classical input properties proved for this word. -/
theorem characteristic_factor_tree_indices {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a)
    {d n : Nat} (hd : 0 < d) (hn : d + 2 ≤ n) (x : Bool)
    (hrun : ∀ i < d, characteristicWord a i = x) (hchange : characteristicWord a d ≠ x) :
    (factorVertices (characteristicWord a) n).card = (n + 1) * (n + 2) / 2 ∧
    albertsonOfWord (characteristicWord a) n = 4 * (n : ℤ) - 2 * d ∧
    quadraticAlbertsonOfWord (characteristicWord a) n = 18 * (n : ℤ) - 10 * d - 2 ∧
    firstZagrebOfWord (characteristicWord a) n = 2 * (n : ℤ) ^ 2 + 8 * n - 4 ∧
    secondZagrebOfWord (characteristicWord a) n = 2 * (n : ℤ) ^ 2 + 10 * n - 11 + d :=
  factor_tree_indices_of_word _ hd hn x hrun hchange (characteristic_complexity a ha ha' hirr)
    (characteristic_rightSpecial_eq_reversedPrefix ha ha' hirr)

/-- The numerical rows apply to the characteristic words themselves. -/
theorem characteristic_depth_eight_table_row {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a)
    {d : Nat} (hd : 0 < d) (hd' : d ≤ 4) (x : Bool)
    (hrun : ∀ i < d, characteristicWord a i = x) (hchange : characteristicWord a d ≠ x) :
    (d, (factorVertices (characteristicWord a) 8).card, albertsonOfWord (characteristicWord a) 8,
      quadraticAlbertsonOfWord (characteristicWord a) 8, firstZagrebOfWord (characteristicWord a) 8,
      secondZagrebOfWord (characteristicWord a) 8) ∈ depthEightTable :=
  depth_eight_table_row _ hd hd' x hrun hchange (characteristic_complexity a ha ha' hirr)
    (characteristic_rightSpecial_eq_reversedPrefix ha ha' hirr)

end Thesis.FactorTree
