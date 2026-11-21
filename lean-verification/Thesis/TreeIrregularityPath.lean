import Thesis.TreeIrregularityLower
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Hasse

open SimpleGraph
open scoped BigOperators

namespace Thesis.TreeIrregularity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
private theorem two_le_maxDegree_of_tree (hT : G.IsTree) (hV : 3 ≤ Fintype.card V) :
    2 ≤ G.maxDegree := by
  by_contra! hm
  have hd : (∑ v, G.degree v) ≤ ∑ _ : V, 1 := by
    apply Finset.sum_le_sum
    intro v _
    have := G.degree_le_maxDegree v
    omega
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hd
  rw [G.sum_degrees_eq_twice_card_edges] at hd
  have hc := hT.card_edgeFinset
  omega

theorem quadraticIrregularity_eq_six_of_path (hT : G.IsTree)
    (hV : 3 ≤ Fintype.card V) (hp : SpanningPath G) : quadraticIrregularity G = 6 := by
  have he : G.maxDegree = 2 :=
    le_antisymm (maxDegree_le_two_of_spanningPath hp) (two_le_maxDegree_of_tree hT hV)
  rw [(quadraticIrregularity_lower_eq_iff_path_or_unique_branch hT).2 (Or.inl hp), he]
  decide

theorem quadraticIrregularity_ge_twentyFour_of_not_path (hT : G.IsTree) (hp : ¬ SpanningPath G) :
    24 ≤ quadraticIrregularity G := by
  have hDelta : 3 ≤ G.maxDegree := by
    by_contra! hm
    exact hp (spanningPath_of_maxDegree_le_two hT (by omega))
  have hD : (3 : ℤ) ≤ G.maxDegree := by exact_mod_cast hDelta
  have hSq : (8 : ℤ) ≤ (G.maxDegree : ℤ) ^ 2 - 1 := by
    nlinarith [sq_nonneg ((G.maxDegree : ℤ) - 3)]
  calc
    24 = (3 : ℤ) * 8 := by decide
    _ ≤ (G.maxDegree : ℤ) * ((G.maxDegree : ℤ) ^ 2 - 1) :=
      mul_le_mul hD hSq (by decide) (by positivity)
    _ ≤ _ := quadraticIrregularity_lower_bound hT

local instance (n : Nat) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

private def pathEdge {n : Nat} (i : Fin n) : Sym2 (Fin (n + 1)) := s(i.castSucc, i.succ)

private theorem pathEdge_injective (n : Nat) : Function.Injective (@pathEdge n) := by
  intro i j h
  rcases Sym2.eq_iff.1 h with h | h
  · exact Fin.ext (congrArg (fun x : Fin (n + 1) => x.val) h.1)
  · have h₁ := congrArg (fun x : Fin (n + 1) => x.val) h.1
    have h₂ := congrArg (fun x : Fin (n + 1) => x.val) h.2
    change i.val = j.val + 1 at h₁
    change i.val + 1 = j.val at h₂
    omega

private theorem pathGraph_edgeFinset (n : Nat) :
    (pathGraph (n + 1)).edgeFinset = Finset.univ.image (@pathEdge n) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    change (s(u, v) ∈ (pathGraph (n + 1)).edgeFinset) ↔ _
    simp only [mem_edgeFinset, mem_edgeSet, pathGraph_adj, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · refine ⟨⟨u.val, by have := v.isLt; omega⟩, Sym2.eq_iff.2 (Or.inl ⟨?_, ?_⟩)⟩
        · exact Fin.ext rfl
        · exact Fin.ext h
      · refine ⟨⟨v.val, by have := u.isLt; omega⟩, Sym2.eq_iff.2 (Or.inr ⟨?_, ?_⟩)⟩
        · exact Fin.ext rfl
        · exact Fin.ext h
    · rintro ⟨i, hi⟩
      rcases Sym2.eq_iff.1 hi with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · left
        simp [← hu, ← hv]
      · right
        simp [← hu, ← hv]

private theorem pathGraph_card_edges (n : Nat) : (pathGraph (n + 1)).edgeFinset.card = n := by
  rw [pathGraph_edgeFinset, Finset.card_image_of_injective _ (pathEdge_injective n)]
  simp

theorem pathGraph_isTree (n : Nat) : (pathGraph (n + 1)).IsTree := by
  refine isTree_iff_connected_and_card.2 ⟨pathGraph_connected n, ?_⟩
  simp only [Nat.card_eq_fintype_card, ← edgeFinset_card, pathGraph_card_edges, Fintype.card_fin]

private theorem pathGraph_maxDegree_le_two (n : Nat) : (pathGraph n).maxDegree ≤ 2 := by
  classical
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro u
  let f : Fin n ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
  have hs : ((pathGraph n).neighborFinset u).map f ⊆ {u.val - 1, u.val + 1} := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 ha
    have h := pathGraph_adj.1 ((SimpleGraph.mem_neighborFinset _ _ _).1 hv)
    simp only [f, Function.Embedding.coeFn_mk, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hc := (Finset.card_le_card hs).trans Finset.card_le_two
  simpa using hc

theorem pathGraph_quadraticIrregularity {n : Nat} (hn : 3 ≤ n) :
    quadraticIrregularity (pathGraph n) = 6 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := n) (by omega)
  have hT := pathGraph_isTree k
  apply quadraticIrregularity_eq_six_of_path hT (by simpa using hn)
  exact spanningPath_of_maxDegree_le_two hT (pathGraph_maxDegree_le_two _)

/-- The strict comparison with (P_n) from `pron2`. -/
theorem quadraticIrregularity_pathGraph_lt (hT : G.IsTree)
    (hV : 5 ≤ Fintype.card V) (hp : ¬ SpanningPath G) :
    quadraticIrregularity (pathGraph (Fintype.card V)) < quadraticIrregularity G := by
  rw [pathGraph_quadraticIrregularity (by omega)]
  exact (by decide : (6 : ℤ) < 24).trans_le (quadraticIrregularity_ge_twentyFour_of_not_path hT hp)

end Thesis.TreeIrregularity
