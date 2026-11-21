import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Thesis.TreeIrregularity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The quadratic contribution of one undirected edge. -/
def quadraticEdgeWeight : Sym2 V → ℤ :=
  Sym2.lift ⟨fun u v => |(G.degree u : ℤ) ^ 2 - (G.degree v : ℤ) ^ 2|,
    fun _ _ => abs_sub_comm _ _⟩

omit [DecidableEq V] in
@[simp] theorem quadraticEdgeWeight_pair (u v : V) :
    quadraticEdgeWeight G s(u, v) = |(G.degree u : ℤ) ^ 2 - (G.degree v : ℤ) ^ 2| := rfl

/-- The quadratic irregularity index from Section 5.1. -/
def quadraticIrregularity : ℤ :=
  ∑ e ∈ G.edgeFinset, quadraticEdgeWeight G e

omit [DecidableEq V] in
theorem quadraticEdgeWeight_nonneg (e : Sym2 V) : 0 ≤ quadraticEdgeWeight G e := by
  induction e using Sym2.inductionOn with
  | _ u v => exact abs_nonneg _

/-- A star on a finite vertex set with prescribed centre. -/
def starGraph (c : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (u = c ∨ v = c)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless _ h := h.1 rfl

instance (c : V) : DecidableRel (starGraph c).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (_ = c ∨ _ = c)))

@[simp] theorem starGraph_degree_center (c : V) : (starGraph c).degree c = Fintype.card V - 1 := by
  have h : (starGraph c).neighborFinset c = Finset.univ.erase c := by
    ext v
    simp [starGraph, ne_comm]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, h, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

@[simp] theorem starGraph_degree_leaf (c v : V) (hvc : v ≠ c) : (starGraph c).degree v = 1 := by
  have h : (starGraph c).neighborFinset v = {c} := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, starGraph, hvc, false_or, Finset.mem_singleton]
    constructor
    · exact And.right
    · rintro rfl
      exact ⟨hvc, rfl⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, h, Finset.card_singleton]

private theorem starGraph_edgeFinset_eq_incidence (c : V) :
    (starGraph c).edgeFinset = (starGraph c).incidenceFinset c := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.incidenceFinset_eq_filter, Finset.mem_filter]
    simp [starGraph, Sym2.mem_iff, eq_comm]

theorem starGraph_edge_count (c : V) : (starGraph c).edgeFinset.card = Fintype.card V - 1 := by
  rw [starGraph_edgeFinset_eq_incidence, SimpleGraph.card_incidenceFinset_eq_degree,
    starGraph_degree_center]

theorem starGraph_isTree (c : V) : (starGraph c).IsTree := by
  haveI : Nonempty V := ⟨c⟩
  have hreach (v : V) : (starGraph c).Reachable c v := by
    by_cases h : c = v
    · subst v
      exact .refl _
    · exact (SimpleGraph.Walk.cons (show (starGraph c).Adj c v from ⟨h, Or.inl rfl⟩)
        .nil).reachable
  apply SimpleGraph.isTree_iff_connected_and_card.2
  refine ⟨SimpleGraph.Connected.mk (fun u v => (hreach u).symm.trans (hreach v)), ?_⟩
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, starGraph_edge_count]
  exact Nat.sub_add_cancel Fintype.card_pos

private theorem starGraph_le_of_degree (c : V) (h : G.degree c = Fintype.card V - 1) :
    starGraph c ≤ G := by
  have hs : G.neighborFinset c ⊆ Finset.univ.erase c := by
    intro v hv
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact (G.ne_of_adj ((G.mem_neighborFinset _ _).1 hv)).symm
  have he := Finset.eq_of_subset_of_card_le hs (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      SimpleGraph.card_neighborFinset_eq_degree, h])
  have hadj (v : V) (hv : v ≠ c) : G.Adj c v := by
    rw [← G.mem_neighborFinset, he]
    simp [hv]
  rintro u v ⟨hne, rfl | rfl⟩
  · exact hadj v hne.symm
  · exact (hadj u hne).symm

/-- A tree with a universal vertex has exactly the edges of a star. -/
theorem eq_starGraph_of_full_degree (hT : G.IsTree) (c : V)
    (hc : G.degree c = Fintype.card V - 1) : G = starGraph c := by
  have hsub := SimpleGraph.edgeFinset_mono (starGraph_le_of_degree G c hc)
  have he : (starGraph c).edgeFinset = G.edgeFinset := Finset.eq_of_subset_of_card_le hsub (by
    rw [starGraph_edge_count]
    have h := hT.card_edgeFinset
    omega)
  exact le_antisymm (SimpleGraph.edgeFinset_subset_edgeFinset.1 he.ge)
    (SimpleGraph.edgeFinset_subset_edgeFinset.1 he.le)

/-- The maximum degree bound for a tree which is not a star. -/
theorem maxDegree_le_of_not_star [Nonempty V] (hT : G.IsTree)
    (hn : ¬ ∃ c, G = starGraph c) : G.maxDegree ≤ Fintype.card V - 2 := by
  obtain ⟨c, hc⟩ := G.exists_maximal_degree_vertex
  have hlt := G.degree_lt_card_verts c
  have hne : G.degree c ≠ Fintype.card V - 1 := fun he =>
    hn ⟨c, eq_starGraph_of_full_degree G hT c he⟩
  omega

omit [DecidableEq V] in
theorem quadraticEdgeWeight_le_maxDegree (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    quadraticEdgeWeight G e ≤ (G.maxDegree : ℤ) ^ 2 - 1 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have ha : G.Adj u v := by simpa using he
    have hu : 1 ≤ (G.degree u : ℤ) := by
      exact_mod_cast (G.degree_pos_iff_exists_adj u).2 ⟨v, ha⟩
    have hv : 1 ≤ (G.degree v : ℤ) := by
      exact_mod_cast (G.degree_pos_iff_exists_adj v).2 ⟨u, ha.symm⟩
    have hu' : (G.degree u : ℤ) ≤ G.maxDegree := by exact_mod_cast G.degree_le_maxDegree u
    have hv' : (G.degree v : ℤ) ≤ G.maxDegree := by exact_mod_cast G.degree_le_maxDegree v
    rw [quadraticEdgeWeight_pair, abs_le]
    constructor <;> nlinarith [sq_nonneg ((G.degree u : ℤ) - 1), sq_nonneg ((G.degree v : ℤ) - 1),
      mul_nonneg (sub_nonneg.2 hu') (show 0 ≤ (G.maxDegree : ℤ) + G.degree u by positivity),
      mul_nonneg (sub_nonneg.2 hv') (show 0 ≤ (G.maxDegree : ℤ) + G.degree v by positivity)]

omit [DecidableEq V] in
theorem quadraticIrregularity_le_of_tree (hT : G.IsTree) :
    quadraticIrregularity G ≤ ((Fintype.card V : ℤ) - 1) * ((G.maxDegree : ℤ) ^ 2 - 1) := by
  unfold quadraticIrregularity
  calc
    _ ≤ ∑ _ ∈ G.edgeFinset, ((G.maxDegree : ℤ) ^ 2 - 1) :=
      Finset.sum_le_sum fun e he => quadraticEdgeWeight_le_maxDegree G e he
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have he := congrArg (fun n : Nat => (n : ℤ)) hT.card_edgeFinset
      push_cast at he
      rw [show (G.edgeFinset.card : ℤ) = Fintype.card V - 1 by omega]

theorem starGraph_quadraticIrregularity (c : V) (hV : 3 ≤ Fintype.card V) :
    quadraticIrregularity (starGraph c) =
      (Fintype.card V : ℤ) * ((Fintype.card V : ℤ) - 1) * ((Fintype.card V : ℤ) - 2) := by
  have he (e : Sym2 V) (hm : e ∈ (starGraph c).edgeFinset) :
      quadraticEdgeWeight (starGraph c) e = ((Fintype.card V : ℤ) - 1) ^ 2 - 1 := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have ha : (starGraph c).Adj u v := by simpa using hm
      change u ≠ v ∧ (u = c ∨ v = c) at ha
      have hcard : 1 ≤ (Fintype.card V : ℤ) - 1 := by omega
      rcases ha with ⟨hne, rfl | rfl⟩
      · rw [quadraticEdgeWeight_pair, starGraph_degree_center, starGraph_degree_leaf _ _ hne.symm,
          Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_one, one_pow, abs_of_nonneg]
        nlinarith
      · rw [quadraticEdgeWeight_pair, abs_sub_comm, starGraph_degree_center,
          starGraph_degree_leaf _ _ hne, Nat.cast_sub (by omega : 1 ≤ Fintype.card V),
          Nat.cast_one, one_pow, abs_of_nonneg]
        nlinarith
  unfold quadraticIrregularity
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const, nsmul_eq_mul, starGraph_edge_count]
  rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_one]
  ring

/-- The strict maximum in the corrected starred proposition in Section 5.1. -/
theorem quadraticIrregularity_lt_starGraph (hT : G.IsTree) (hV : 3 ≤ Fintype.card V)
    (hG : ¬ ∃ c, G = starGraph c) (c : V) :
    quadraticIrregularity G < quadraticIrregularity (starGraph c) := by
  have hmax : (G.maxDegree : ℤ) ≤ (Fintype.card V : ℤ) - 2 := by
    haveI : Nonempty V := ⟨c⟩
    have h := maxDegree_le_of_not_star G hT hG
    omega
  have hbound := quadraticIrregularity_le_of_tree G hT
  rw [starGraph_quadraticIrregularity c hV]
  let n : ℤ := Fintype.card V
  have hn : 3 ≤ n := by dsimp [n]; exact_mod_cast hV
  have hmax' : 0 ≤ (G.maxDegree : ℤ) := by positivity
  have hsq : (G.maxDegree : ℤ) ^ 2 - 1 < (n - 1) ^ 2 - 1 := by
    nlinarith [mul_pos (show 0 < (n - 1) - G.maxDegree by omega)
      (show 0 < (n - 1) + G.maxDegree by omega)]
  calc
    _ ≤ (n - 1) * ((G.maxDegree : ℤ) ^ 2 - 1) := hbound
    _ < (n - 1) * ((n - 1) ^ 2 - 1) := mul_lt_mul_of_pos_left hsq (by omega)
    _ = n * (n - 1) * (n - 2) := by ring

end Thesis.TreeIrregularity
