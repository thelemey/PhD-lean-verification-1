import Thesis.FactorTreeEdgeCounts

open scoped BigOperators
open Thesis.ThueMorse (factorLanguage)

namespace Thesis.FactorTree

/-- The parent and child of an edge, as vertices indexed by length. -/
def factorEdgeParent (e : Σ k : Nat, Fin (k + 1) → Bool) : Σ k : Nat, Fin k → Bool :=
  ⟨e.1, wordPrefix e.2⟩

def factorEdgeChild (e : Σ k : Nat, Fin (k + 1) → Bool) : Σ k : Nat, Fin k → Bool :=
  ⟨e.1 + 1, e.2⟩

private theorem card_outgoing (w : Nat → Bool) (n k : Nat) (u : Fin k → Bool) :
    ((factorEdges w n).filter (fun e => factorEdgeParent e = ⟨k, u⟩)).card =
      if k < n then (children w k u).card else 0 := by
  rw [card_filter_factorEdges]
  calc
    _ = ∑ j ∈ Finset.range n, if j = k then (children w k u).card else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = k
      · subst j
        simp [factorEdgeParent, Sigma.mk.inj_iff, heq_iff_eq, children]
      · simp [factorEdgeParent, Sigma.mk.inj_iff, hj]
    _ = _ := by simp [Finset.mem_range]

private theorem card_incoming (w : Nat → Bool) (n k : Nat) (hkn : k ≤ n)
    (u : Fin k → Bool) (hu : u ∈ factorLanguage w k) :
    ((factorEdges w n).filter (fun e => factorEdgeChild e = ⟨k, u⟩)).card =
      if k = 0 then 0 else 1 := by
  rw [card_filter_factorEdges]
  cases k with
  | zero => simp [factorEdgeChild, Sigma.mk.inj_iff]
  | succ k =>
    calc
      _ = ∑ j ∈ Finset.range n, if j = k then (1 : Nat) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = k
        · subst j
          simp [factorEdgeChild, Sigma.mk.inj_iff, heq_iff_eq, Finset.filter_eq', hu]
        · simp [factorEdgeChild, Sigma.mk.inj_iff, hj]
      _ = _ := by simp [Finset.mem_range, show k < n by omega]

/-- The degree used in the index formulas is exactly the number of edges
incident to the given vertex. The root has no incoming edge, and every
other vertex has one. At depth n there are no outgoing edges. -/
theorem truncatedDegree_eq_card_incident (w : Nat → Bool) (n k : Nat) (u : Fin k → Bool)
    (hu : (⟨k, u⟩ : Σ j : Nat, Fin j → Bool) ∈ factorVertices w n) :
    truncatedDegree w n k u = ((factorEdges w n).filter (fun e =>
      factorEdgeChild e = ⟨k, u⟩ ∨ factorEdgeParent e = ⟨k, u⟩)).card := by
  obtain ⟨hk, hu⟩ := Finset.mem_sigma.1 hu
  have hk' : k < n + 1 := Finset.mem_range.1 hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp hk'
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  · rw [card_incoming w n k hkn u hu, card_outgoing, truncatedDegree]
  · apply Finset.disjoint_filter.2
    intro e _ hchild hparent
    have hc := congrArg Sigma.fst hchild
    have hp := congrArg Sigma.fst hparent
    change e.1 + 1 = k at hc
    change e.1 = k at hp
    omega

end Thesis.FactorTree
