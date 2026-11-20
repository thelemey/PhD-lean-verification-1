import Thesis.FactorTree
import Thesis.ThueMorseComplexity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.OfFn

open scoped BigOperators
open Thesis.ThueMorse (window factorLanguage complexity mem_factorLanguage factorLanguage_prefix_image)

namespace Thesis.FactorTree

def wordPrefix {A : Type*} {k : Nat} (f : Fin (k + 1) → A) : Fin k → A :=
  fun j => f (Fin.castSucc j)

/-- The children of a word in the prefix tree are its one-letter right
extensions which occur as factors. -/
noncomputable def children (w : Nat → Bool) (k : Nat) (u : Fin k → Bool) :
    Finset (Fin (k + 1) → Bool) :=
  (factorLanguage w (k + 1)).filter (fun v => wordPrefix v = u)

theorem children_nonempty (w : Nat → Bool) (k : Nat) (u : Fin k → Bool)
    (hu : u ∈ factorLanguage w k) : (children w k u).Nonempty := by
  obtain ⟨i, rfl⟩ := (mem_factorLanguage _ _ _).1 hu
  refine ⟨window w (k + 1) i, Finset.mem_filter.2 ?_⟩
  exact ⟨(mem_factorLanguage _ _ _).2 ⟨i, rfl⟩, rfl⟩

theorem children_card_le_two (w : Nat → Bool) (k : Nat) (u : Fin k → Bool) :
    (children w k u).card ≤ 2 := by
  apply le_trans (Finset.card_le_card_of_injOn (fun v => v (Fin.last k))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _ ) ?_) (by decide)
  intro v hv z hz he
  have hv' := (Finset.mem_filter.1 hv).2
  have hz' := (Finset.mem_filter.1 hz).2
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact congrFun (hv'.trans hz'.symm) j
  · exact he

/-- The right-special factors are exactly the binary factors with two
different one-letter extensions. -/
noncomputable def rightSpecials (w : Nat → Bool) (k : Nat) : Finset (Fin k → Bool) :=
  (factorLanguage w k).filter (fun u => (children w k u).card = 2)

theorem complexity_succ_eq_add_rightSpecials (w : Nat → Bool) (k : Nat) :
    complexity w (k + 1) = complexity w k + (rightSpecials w k).card := by
  classical
  have hp : ∀ v ∈ factorLanguage w (k + 1), wordPrefix v ∈ factorLanguage w k := by
    intro v hv
    rw [← factorLanguage_prefix_image w k]
    exact Finset.mem_image.2 ⟨v, hv, rfl⟩
  have he : complexity w (k + 1) =
      ∑ u ∈ factorLanguage w k, (children w k u).card :=
    Finset.card_eq_sum_card_fiberwise hp
  rw [he]
  have hcount : (∑ u ∈ factorLanguage w k, (children w k u).card) =
      ∑ u ∈ factorLanguage w k, (1 + if (children w k u).card = 2 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro u hu
    have h₁ := Finset.card_pos.2 (children_nonempty w k u hu)
    have h₂ := children_card_le_two w k u
    split_ifs <;> omega
  rw [hcount, Finset.sum_add_distrib]
  simp [complexity, rightSpecials]

/-- The implication in the cited Sturmian fact (F1): when the
complexity rises from k+1 to k+2, the right-special factor is unique. -/
theorem unique_right_special_of_complexity (w : Nat → Bool) (k : Nat)
    (hk : complexity w k = k + 1) (hk' : complexity w (k + 1) = k + 2) :
    ∃! u : Fin k → Bool, u ∈ rightSpecials w k := by
  have hcard := complexity_succ_eq_add_rightSpecials w k
  have hc : (rightSpecials w k).card = 1 := by omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hc
  refine ⟨u, by simp [hu], ?_⟩
  intro v hv
  simpa [hu] using hv

/-- The degree in the truncated factor tree, counting the parent edge
at a positive level and the children below the final level. -/
noncomputable def truncatedDegree (w : Nat → Bool) (n k : Nat) (u : Fin k → Bool) : Nat :=
  (if k = 0 then 0 else 1) + if k < n then (children w k u).card else 0

/-- Internal nonroot vertices have degree three precisely when their
factors are right-special. The other internal vertices have degree two. -/
theorem internal_degree_eq (w : Nat → Bool) {n k : Nat} (h0 : 0 < k) (hk : k < n)
    (u : Fin k → Bool) (hu : u ∈ factorLanguage w k) :
    truncatedDegree w n k u = if u ∈ rightSpecials w k then 3 else 2 := by
  classical
  have h₁ := Finset.card_pos.2 (children_nonempty w k u hu)
  have h₂ := children_card_le_two w k u
  simp only [truncatedDegree, h0.ne', hk, rightSpecials, Finset.mem_filter, hu, true_and,
    if_false, if_true]
  split_ifs <;> omega

theorem leaf_degree_eq_one (w : Nat → Bool) {n : Nat} (hn : 0 < n) (u : Fin n → Bool) :
    truncatedDegree w n n u = 1 := by simp [truncatedDegree, hn.ne']

theorem root_degree_eq_two (w : Nat → Bool) {n : Nat} (hn : 0 < n)
    (u : Fin 0 → Bool) (h : complexity w 1 = 2) :
    truncatedDegree w n 0 u = 2 := by
  have he : children w 0 u = factorLanguage w 1 := by
    ext v
    rw [children, Finset.mem_filter]
    exact and_iff_left_of_imp (fun _ => Subsingleton.elim _ _)
  simpa [truncatedDegree, hn, he, complexity] using h

/-- The last internal level contributes exactly two special-parent
edges to leaves. At any preceding positive level there are likewise exactly two
outgoing edges from its single right-special vertex. -/
theorem edges_from_special_card (w : Nat → Bool) (k : Nat)
    (hk : complexity w k = k + 1) (hk' : complexity w (k + 1) = k + 2) :
    ((factorLanguage w (k + 1)).filter (fun v => wordPrefix v ∈ rightSpecials w k)).card = 2 := by
  have hcard := complexity_succ_eq_add_rightSpecials w k
  have hc : (rightSpecials w k).card = 1 := by omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hc
  have hm : u ∈ rightSpecials w k := by simp [hu]
  have he : (children w k u).card = 2 := (Finset.mem_filter.1 hm).2
  simpa [hu, children] using he

/-- There is an edge between the two successive right-special levels
when the special factor at the larger level extends the other. -/
def specialEdgeAt (w : Nat → Bool) (k : Nat) : Prop :=
  ∃ v ∈ rightSpecials w (k + 1), wordPrefix v ∈ rightSpecials w k

private theorem ofFn_prefix_append {k : Nat} (v : Fin (k + 1) → Bool) :
    List.ofFn v = List.ofFn (wordPrefix v) ++ [v (Fin.last k)] :=
  by simpa [wordPrefix, List.concat_eq_append] using List.ofFn_succ' v

/-- The adjacent special vertices are exactly the adjacent reversed
prefixes, under the reversal property (F2) cited in the thesis. -/
theorem specialEdgeAt_iff_reversed_prefix (w : Nat → Bool) (k : Nat)
    (hwidth : ∀ j, complexity w j = j + 1)
    (hreversal : ∀ j (u : Fin j → Bool), u ∈ rightSpecials w j →
      List.ofFn u = reversedPrefix w j) :
    specialEdgeAt w k ↔ ∃ a, reversedPrefix w (k + 1) = reversedPrefix w k ++ [a] := by
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v (Fin.last k), ?_⟩
    rw [← hreversal _ v hv, ← hreversal _ (wordPrefix v) h, ← ofFn_prefix_append]
  · rintro ⟨a, ha⟩
    obtain ⟨u, hu, _⟩ := unique_right_special_of_complexity w k (hwidth _) (hwidth _)
    obtain ⟨v, hv, _⟩ := unique_right_special_of_complexity w (k + 1) (hwidth _) (hwidth _)
    refine ⟨v, hv, ?_⟩
    rw [← hreversal _ u hu, ← hreversal _ v hv, ofFn_prefix_append] at ha
    have ht := congrArg (List.take k) ha
    simp only [List.take_append_of_le_length (by simp : k ≤ (List.ofFn (wordPrefix v)).length),
      List.take_append_of_le_length (by simp : k ≤ (List.ofFn u).length),
      List.take_of_length_le (by simp : (List.ofFn (wordPrefix v)).length ≤ k),
      List.take_of_length_le (by simp : (List.ofFn u).length ≤ k)] at ht
    rwa [List.ofFn_inj.1 ht]

/-- The actual number of edges joining successive internal special
vertices, under the two classical Sturmian language properties. -/
theorem count_special_edges (w : Nat → Bool) {d n : Nat} (hd : 0 < d) (hn : d + 2 ≤ n)
    (x : Bool) (hrun : ∀ i < d, w i = x) (hchange : w d ≠ x)
    (hwidth : ∀ j, complexity w j = j + 1)
    (hreversal : ∀ j (u : Fin j → Bool), u ∈ rightSpecials w j →
      List.ofFn u = reversedPrefix w j) :
    (List.range' 1 (n - 2)).countP (fun k => by classical exact decide (specialEdgeAt w k)) = d - 1 := by
  classical
  apply count_adjacent_reversedPrefixes w hd hn x hrun hchange
  intro k _ _
  rw [decide_eq_true_eq, specialEdgeAt_iff_reversed_prefix w k hwidth hreversal]

end Thesis.FactorTree
