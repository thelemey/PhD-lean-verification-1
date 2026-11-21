import Thesis.PolyominoGridContacts
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open SimpleGraph

namespace Thesis.Polyomino

/-- Side adjacency in the second cutting model in the remark after Theorem 4.2.1.
Each edge represents one *unit* common side. -/
def sideGraph (cells : List Cell) : SimpleGraph (CellIn cells) where
  Adj p q := RemainingAdjacent [] p q
  symm := by
    rintro p q ⟨l,h,hl⟩
    exact ⟨l,h.symm,hl⟩
  loopless := by
    rintro p ⟨l,(h|h),_⟩ <;> rcases h with ⟨eq,_⟩|⟨eq,_⟩
    all_goals
      obtain ⟨⟨x,y⟩,_⟩ := p
      simp at eq

private theorem sideGraph_adj_iff {c : List Cell} {p q : CellIn c} :
    (sideGraph c).Adj p q ↔
    (q.val = (p.val.1+1,p.val.2) ∨ q.val = (p.val.1,p.val.2+1)) ∨
    (p.val = (q.val.1+1,q.val.2) ∨ p.val = (q.val.1,q.val.2+1)) := by
  change (∃ l, SharedSide _ _ l ∧ l ∉ ([] : List Line)) ↔ _
  simp only [List.not_mem_nil, and_true, SharedSide, PositiveSide, exists_or, exists_and_right,
    exists_eq, and_true]
  simp

instance (c : List Cell) : DecidableRel (sideGraph c).Adj :=
  fun _ _ => decidable_of_iff' _ sideGraph_adj_iff

theorem sideGraph_reachable_iff {cells : List Cell} (p q : CellIn cells) :
    (sideGraph cells).Reachable p q ↔ SamePart [] p q :=
  reachable_iff_reflTransGen p q

theorem sideGraph_connected_iff (cells : List Cell) [Nonempty (CellIn cells)] :
    (sideGraph cells).Connected ↔ SideConnected cells := by
  rw [SimpleGraph.connected_iff]
  constructor
  · exact fun ⟨h,_⟩ p q => (sideGraph_reachable_iff _ _).1 (h p q)
  · exact fun h => ⟨fun p q => (sideGraph_reachable_iff _ _).2 (h p q),inferInstance⟩

/-- Cutting one unit edge per operation leaves individual vertices exactly
when every original graph edge occurs in the list. Repetitions are allowed. -/
theorem unitCuts_separate_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (cuts : List (Sym2 V)) :
    (∀ p q, (G.deleteEdges (cuts.toFinset : Set (Sym2 V))).Reachable p q → p=q) ↔
      G.edgeSet ⊆ (cuts.toFinset : Set (Sym2 V)) := by
  let H := G.deleteEdges (cuts.toFinset : Set (Sym2 V))
  have he : (∀ p q, H.Reachable p q → p=q) ↔ H = ⊥ := by
    constructor
    · intro h
      apply le_antisymm _ bot_le
      intro p q hpq
      exact (hpq.ne (h p q hpq.reachable)).elim
    · intro h p q
      rw [h,reachable_bot]
      exact id
  rw [he,← edgeSet_eq_empty]
  simp only [H,edgeSet_deleteEdges,Set.diff_eq_empty]

/-- The minimum in the unit-edge model is the number of inner edges, as
opposed to the count of distinct complete grid lines in the theorem. -/
theorem minimum_unit_edge_cuts (cells : List Cell) :
    let G := sideGraph cells
    (∃ cuts : List (Sym2 (CellIn cells)), (∀ p q, (G.deleteEdges (cuts.toFinset : Set _)).Reachable p q → p=q) ∧
      cuts.length = G.edgeFinset.card) ∧
    ∀ cuts : List (Sym2 (CellIn cells)), (∀ p q, (G.deleteEdges (cuts.toFinset : Set _)).Reachable p q → p=q) →
      G.edgeFinset.card ≤ cuts.length := by
  intro G
  refine ⟨⟨G.edgeFinset.toList, (unitCuts_separate_iff _ _).2 ?_, by simp⟩,?_⟩
  · simp
  · intro cuts h
    have sub := (unitCuts_separate_iff G cuts).1 h
    exact (Finset.card_le_card (show G.edgeFinset ⊆ cuts.toFinset by simpa using sub)).trans cuts.toFinset_card_le

/-- In a nonempty side-connected polyomino, the unit-edge count equals N−1
exactly when the adjacency graph is a tree. -/
theorem unit_edges_eq_cells_sub_one_iff_tree (cells : List Cell) [Nonempty (CellIn cells)]
    (hc : SideConnected cells) :
    (sideGraph cells).edgeFinset.card = Fintype.card (CellIn cells)-1 ↔ (sideGraph cells).IsTree := by
  rw [isTree_iff_connected_and_card, and_iff_right ((sideGraph_connected_iff cells).2 hc),
    Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← edgeFinset_card]
  have hn := Fintype.card_pos (α := CellIn cells)
  omega

/-- The explicit comparison in the remark: four unit edges but two complete
grid lines for the same 2-by-2 square. -/
theorem two_by_two_cut_models :
    (sideGraph (rectangle 2 2)).edgeFinset.card = 4 ∧
      (internalLines (rectangle 2 2)).length = 2 := by decide +kernel

end Thesis.Polyomino
