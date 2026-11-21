import Thesis.FactorTreeDegrees
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open scoped BigOperators
open Thesis.ThueMorse (factorLanguage mem_factorLanguage)

namespace Thesis.FactorTree

abbrev FactorVertex (w : Nat → Bool) (n : Nat) := ↥(factorVertices w n)
abbrev FactorEdge (w : Nat → Bool) (n : Nat) := ↥(factorEdges w n)

variable {w : Nat → Bool} {n : Nat}

def parentVertex (e : FactorEdge w n) : FactorVertex w n :=
  ⟨factorEdgeParent e.val, (edge_endpoints_mem_vertices w n e.val e.property).1⟩

def childVertex (e : FactorEdge w n) : FactorVertex w n :=
  ⟨factorEdgeChild e.val, (edge_endpoints_mem_vertices w n e.val e.property).2⟩

private theorem parent_depth (e : FactorEdge w n) : (parentVertex e).val.1 = e.val.1 := rfl

private theorem child_depth (e : FactorEdge w n) : (childVertex e).val.1 = e.val.1 + 1 := rfl

private theorem childVertex_injective : Function.Injective (childVertex (w := w) (n := n)) := by
  rintro ⟨⟨k, u⟩, hu⟩ ⟨⟨l, v⟩, hv⟩ h
  have hdepth := congrArg (fun x : FactorVertex w n => x.val.1) h
  change k + 1 = l + 1 at hdepth
  have heq : l = k := by omega
  subst l
  apply Subtype.ext
  have hchild := congrArg Subtype.val h
  change (⟨k + 1, u⟩ : Σ j : Nat, Fin j → Bool) = ⟨k + 1, v⟩ at hchild
  have he : u = v := by simpa using hchild
  exact congrArg (Sigma.mk k) he

/-- The finite undirected prefix tree of factors in thm:factortree. -/
def factorGraph (w : Nat → Bool) (n : Nat) : SimpleGraph (FactorVertex w n) where
  Adj u v := ∃ e : FactorEdge w n,
    (parentVertex e = u ∧ childVertex e = v) ∨ (parentVertex e = v ∧ childVertex e = u)
  symm := by
    rintro u v ⟨e, hv | hv⟩
    · exact ⟨e, Or.inr hv⟩
    · exact ⟨e, Or.inl hv⟩
  loopless := by
    rintro u ⟨e, hv | hv⟩ <;>
      have h := congrArg (fun v : FactorVertex w n => v.val.1) (hv.1.trans hv.2.symm) <;>
      simp only [parent_depth, child_depth] at h <;> omega

/-- The finite factor represented by a graph vertex. -/
def vertexWord (v : FactorVertex w n) : List Bool := List.ofFn v.val.2

private theorem vertexWord_child (e : FactorEdge w n) :
    vertexWord (childVertex e) =
      vertexWord (parentVertex e) ++ [e.val.2 (Fin.last e.val.1)] := by
  simpa only [vertexWord, childVertex, parentVertex, factorEdgeChild,
    factorEdgeParent, wordPrefix, List.concat_eq_append] using List.ofFn_succ' e.val.2

private theorem parent_child_iff_append (u v : FactorVertex w n) :
    (∃ e : FactorEdge w n, parentVertex e = u ∧ childVertex e = v) ↔
      ∃ a, vertexWord v = vertexWord u ++ [a] := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    exact ⟨_, vertexWord_child e⟩
  · rcases u with ⟨⟨k, f⟩, hu⟩
    rcases v with ⟨⟨l, g⟩, hv⟩
    rintro ⟨a, ha⟩
    change List.ofFn g = List.ofFn f ++ [a] at ha
    have hl : l = k + 1 := by
      simpa only [List.length_ofFn, List.length_append, List.length_singleton]
        using congrArg List.length ha
    subst l
    obtain ⟨hk, hg⟩ := Finset.mem_sigma.1 hv
    have hk' : k + 1 < n + 1 := Finset.mem_range.1 hk
    let e : FactorEdge w n :=
      ⟨⟨k, g⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 (Nat.lt_of_succ_lt_succ hk'), hg⟩⟩
    refine ⟨e, Subtype.ext ?_, rfl⟩
    change (⟨k, wordPrefix g⟩ : Σ j : Nat, Fin j → Bool) = ⟨k, f⟩
    have he : List.ofFn g = List.ofFn (wordPrefix g) ++ [g (Fin.last k)] := vertexWord_child e
    have hprefix : wordPrefix g = f :=
      List.ofFn_inj.1 (List.append_inj_left' (he.symm.trans ha) (by simp))
    exact congrArg (Sigma.mk k) hprefix

/-- Adjacency is precisely appending one letter in either direction. -/
theorem factorGraph_adj_iff_append (u v : FactorVertex w n) :
    (factorGraph w n).Adj u v ↔
      (∃ a, vertexWord v = vertexWord u ++ [a]) ∨
      (∃ a, vertexWord u = vertexWord v ++ [a]) := by
  change (∃ e : FactorEdge w n, _ ∨ _) ↔ _
  rw [exists_or, parent_child_iff_append, parent_child_iff_append]

def graphEdge (e : FactorEdge w n) : Sym2 (FactorVertex w n) :=
  s(parentVertex e, childVertex e)

theorem graphEdge_injective : Function.Injective (graphEdge (w := w) (n := n)) := by
  intro e f h
  rcases Sym2.eq_iff.1 h with ⟨_, hc⟩ | ⟨h₁, h₂⟩
  · exact childVertex_injective hc
  · have hl := congrArg (fun v : FactorVertex w n => v.val.1) h₁
    have hr := congrArg (fun v : FactorVertex w n => v.val.1) h₂
    simp only [parent_depth, child_depth] at hl hr
    omega

noncomputable instance (w : Nat → Bool) (n : Nat) :
    Fintype (factorGraph w n).edgeSet := Fintype.ofFinite _

noncomputable instance (w : Nat → Bool) (n : Nat) (v : FactorVertex w n) :
    Fintype ((factorGraph w n).neighborSet v) := Fintype.ofFinite _

theorem factorGraph_edgeFinset (w : Nat → Bool) (n : Nat) :
    (factorGraph w n).edgeFinset = (factorEdges w n).attach.image graphEdge := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change (∃ f : FactorEdge w n, _) ↔ _
    simp only [Finset.mem_image, Finset.mem_attach, true_and, graphEdge, Sym2.eq_iff]

theorem factorGraph_edge_card (w : Nat → Bool) (n : Nat) :
    (factorGraph w n).edgeFinset.card = (factorEdges w n).card := by
  classical
  rw [factorGraph_edgeFinset, Finset.card_image_of_injective _ graphEdge_injective, Finset.card_attach]

private def root (w : Nat → Bool) (n : Nat) : FactorVertex w n := by
  let u : Fin 0 → Bool := Fin.elim0
  refine ⟨⟨0, u⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 (Nat.zero_lt_succ n), ?_⟩⟩
  exact (mem_factorLanguage _ _ _).2 ⟨0, Subsingleton.elim _ _⟩

theorem factorGraph_connected (w : Nat → Bool) (n : Nat) : (factorGraph w n).Connected := by
  have reach : ∀ k : Nat, ∀ u : Fin k → Bool,
      ∀ hu : (⟨k, u⟩ : Σ j : Nat, Fin j → Bool) ∈ factorVertices w n,
        (factorGraph w n).Reachable (root w n) ⟨⟨k, u⟩, hu⟩ := by
    intro k
    induction k with
    | zero =>
      intro u hu
      have he : (⟨⟨0, u⟩, hu⟩ : FactorVertex w n) = root w n := by
        apply Subtype.ext
        change (⟨0, u⟩ : Σ j : Nat, Fin j → Bool) = ⟨0, Fin.elim0⟩
        rw [Subsingleton.elim u Fin.elim0]
      rw [he]
    | succ k ih =>
      intro u hu
      obtain ⟨hk, hv⟩ := Finset.mem_sigma.1 hu
      have hk' : k + 1 < n + 1 := Finset.mem_range.1 hk
      have he : (⟨k, u⟩ : Σ j : Nat, Fin (j + 1) → Bool) ∈ factorEdges w n :=
        Finset.mem_sigma.2 ⟨Finset.mem_range.2 (Nat.lt_of_succ_lt_succ hk'), hv⟩
      let e : FactorEdge w n := ⟨⟨k, u⟩, he⟩
      have h : (factorGraph w n).Adj (parentVertex e) (childVertex e) := ⟨e, Or.inl ⟨rfl, rfl⟩⟩
      exact (ih (wordPrefix u) (parentVertex e).property).trans h.reachable
  letI : Nonempty (FactorVertex w n) := ⟨root w n⟩
  constructor
  rintro ⟨⟨k, u⟩, hu⟩ ⟨⟨l, v⟩, hv⟩
  exact (reach k u hu).symm.trans (reach l v hv)

theorem factorGraph_isTree (w : Nat → Bool) (n : Nat) : (factorGraph w n).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.2 ⟨factorGraph_connected w n, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, factorGraph_edge_card,
    Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [factorEdges, factorVertices, Finset.card_sigma, Finset.card_sigma, Finset.sum_range_succ']
  have hzero : (factorLanguage w 0).card = 1 := by
    have hroot : factorLanguage w 0 = {Fin.elim0} := by
      ext u
      simp only [mem_factorLanguage, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    rw [hroot, Finset.card_singleton]
  rw [hzero]

end Thesis.FactorTree
