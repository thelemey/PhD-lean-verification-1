import Thesis.TreeIrregularity

open SimpleGraph SimpleGraph.Walk
open scoped BigOperators

namespace Thesis.TreeIrregularity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem snd_takeUntil_of_ne {a b z : V} (p : G.Walk a b)
    (hz : z ∈ p.support) (ha : z ≠ a) : (p.takeUntil z hz).snd = p.snd := by
  cases p with
  | nil => exact (ha (by simpa using hz)).elim
  | cons h q =>
    have hz' : z ∈ q.support := by simpa [ha] using hz
    rw [takeUntil_cons hz' ha.symm h, snd_cons, snd_cons]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem vertex_common_to_branches {a b c z : V} (hT : G.IsAcyclic)
    {p : G.Walk a b} {q : G.Walk a c} (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.snd ≠ q.snd) (hzp : z ∈ p.support) (hzq : z ∈ q.support) : z = a := by
  by_contra hn
  have he := hT.path_unique ⟨p.takeUntil z hzp, hp.takeUntil hzp⟩
    ⟨q.takeUntil z hzq, hq.takeUntil hzq⟩
  have hs := congrArg (fun t : G.Path a z => t.val.snd) he
  apply hd
  simpa only [snd_takeUntil_of_ne p hzp hn, snd_takeUntil_of_ne q hzq hn] using hs

omit [Fintype V] [DecidableRel G.Adj] in
private theorem edges_disjoint_of_snd_ne {a b c : V} (hT : G.IsAcyclic)
    {p : G.Walk a b} {q : G.Walk a c} (hp : p.IsPath) (hq : q.IsPath)
    (hd : p.snd ≠ q.snd) : Disjoint p.edges.toFinset q.edges.toFinset := by
  rw [Finset.disjoint_left]
  intro e hep heq
  rw [List.mem_toFinset] at hep heq
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hu := vertex_common_to_branches hT hp hq hd
      (p.fst_mem_support_of_mem_edges hep) (q.fst_mem_support_of_mem_edges heq)
    have hv := vertex_common_to_branches hT hp hq hd
      (p.snd_mem_support_of_mem_edges hep) (q.snd_mem_support_of_mem_edges heq)
    have hadj : G.Adj u v := p.edges_subset_edgeSet hep
    exact (G.ne_of_adj hadj) (hu.trans hv.symm)

omit [Fintype V] [DecidableRel G.Adj] in
private theorem adj_mem_support_eq_penultimate {a b x : V} (hT : G.IsAcyclic)
    {p : G.Walk a b} (hp : p.IsPath) (hx : G.Adj b x) (hm : x ∈ p.support) :
    x = p.penultimate := by
  have hrev : x ∈ p.reverse.support := by simpa using hm
  have he := hT.path_unique (Path.singleton hx)
    ⟨p.reverse.takeUntil x hrev, hp.reverse.takeUntil hrev⟩
  have hs := congrArg (fun t : G.Path b x => t.val.snd) he
  change x = (p.reverse.takeUntil x hrev).snd at hs
  rw [snd_takeUntil_of_ne _ hrev (G.ne_of_adj hx).symm, snd_reverse] at hs
  exact hs

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem path_concat_of_not_mem {a b x : V} {p : G.Walk a b} (hp : p.IsPath)
    (hx : G.Adj b x) (hm : x ∉ p.support) : (p.concat hx).IsPath := by
  rw [isPath_def, support_concat, List.concat_eq_append, List.nodup_append]
  exact ⟨hp.support_nodup, by simp, by simpa [List.disjoint_left] using hm⟩

omit [DecidableRel G.Adj] in
private theorem path_length_le_card {a b : V} {p : G.Walk a b} (hp : p.IsPath) :
    p.length ≤ Fintype.card V := by
  have hc := Finset.card_le_univ p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup, length_support] at hc
  omega

/-- Starting down any branch, extend a simple path until it meets a leaf. -/
private theorem leaf_path_in_branch {a b : V} (hT : G.IsAcyclic) (hab : G.Adj a b) :
    ∃ z, ∃ p : G.Walk b z, (cons hab p).IsPath ∧ G.degree z = 1 := by
  classical
  let P (n : Nat) : Prop := ∃ z, ∃ p : G.Walk b z, (cons hab p).IsPath ∧ p.length = n
  have h0 : P 0 := ⟨b, nil, IsPath.of_adj hab, rfl⟩
  let k := Nat.findGreatest P (Fintype.card V)
  obtain ⟨z, p, hp, hlen⟩ : P k := Nat.findGreatest_spec (Nat.zero_le _) h0
  let q := cons hab p
  have hq : ¬ q.Nil := by simp [q]
  have ha := (q.adj_penultimate hq).symm
  have he : G.neighborFinset z = {q.penultimate} := by
    ext x
    rw [G.mem_neighborFinset, Finset.mem_singleton]
    refine ⟨fun hx => ?_, fun hx => hx.symm ▸ ha⟩
    apply adj_mem_support_eq_penultimate hT hp hx
    by_contra hm
    have hn := path_concat_of_not_mem hp hx hm
    change (cons hab (p.concat hx)).IsPath at hn
    have hl : (p.concat hx).length = k + 1 := by simp [hlen]
    have hcard := path_length_le_card hn
    simp only [length_cons, hl] at hcard
    have hk := Nat.le_findGreatest (P := P) (show k + 1 ≤ Fintype.card V by omega)
      (show P (k + 1) from ⟨x, p.concat hx, hn, hl⟩)
    change k + 1 ≤ k at hk
    omega
  exact ⟨z, p, hp, by rw [← G.card_neighborFinset_eq_degree, he, Finset.card_singleton]⟩

omit [DecidableRel G.Adj] [Fintype V] [DecidableEq V] in
private theorem walk_weight_triangle {a b : V} (f : V → ℤ) (p : G.Walk a b) :
    |f a - f b| ≤ (p.edges.map
      (Sym2.lift ⟨fun x y => |f x - f y|, fun _ _ => abs_sub_comm _ _⟩)).sum := by
  induction p with
  | nil => simp
  | cons h q ih =>
    simp only [edges_cons, List.map_cons, List.sum_cons, Sym2.lift_mk]
    exact (abs_sub_le _ _ _).trans (add_le_add_left ih _)

private theorem walk_quadratic_triangle {a b : V} {p : G.Walk a b} (hp : p.IsPath) :
    |(G.degree a : ℤ) ^ 2 - (G.degree b : ℤ) ^ 2| ≤
      ∑ e ∈ p.edges.toFinset, quadraticEdgeWeight G e := by
  have h := walk_weight_triangle (G := G) (fun x => (G.degree x : ℤ) ^ 2) p
  simpa only [← List.sum_toFinset _ hp.isTrail.edges_nodup, quadraticEdgeWeight] using h

/-- The edges reached by paths from the root with a given first step. -/
private noncomputable def branchEdges (a b : V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e => ∃ z, ∃ p : G.Walk a z, p.IsPath ∧ p.snd = b ∧ e ∈ p.edges

private theorem edges_subset_branch {a b z : V} {p : G.Walk a z} (hp : p.IsPath) (hs : p.snd = b) :
    p.edges.toFinset ⊆ branchEdges (G := G) a b := by
  classical
  intro e he
  have hm := List.mem_toFinset.1 he
  apply Finset.mem_filter.2
  exact ⟨SimpleGraph.mem_edgeFinset.2 (p.edges_subset_edgeSet hm), z, p, hp, hs, hm⟩

omit [DecidableEq V] in
private theorem branchEdges_subset (a b : V) : branchEdges (G := G) a b ⊆ G.edgeFinset := by
  classical
  exact Finset.filter_subset _ _

private theorem branchEdges_disjoint {a b c : V} (hT : G.IsAcyclic) (hbc : b ≠ c) :
    Disjoint (branchEdges (G := G) a b) (branchEdges (G := G) a c) := by
  classical
  apply Finset.disjoint_left.2
  intro e he hf
  obtain ⟨_, z, p, hzp, hps, hpe⟩ := Finset.mem_filter.1 he
  obtain ⟨_, w, q, hwq, hqs, hqe⟩ := Finset.mem_filter.1 hf
  have hd := edges_disjoint_of_snd_ne hT hzp hwq (by simpa only [hps, hqs] using hbc)
  exact Finset.disjoint_left.1 hd (List.mem_toFinset.2 hpe) (List.mem_toFinset.2 hqe)

private theorem union_branchEdges (hT : G.IsTree) (a : V) :
    (G.neighborFinset a).biUnion (branchEdges (G := G) a) = G.edgeFinset := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.1 he
    exact branchEdges_subset a b hb
  · intro e he
    have addBranch {z : V} (p : G.Walk a z) (hp : p.IsPath) (he : e ∈ p.edges) :
        e ∈ (G.neighborFinset a).biUnion (branchEdges (G := G) a) := by
      have hp₀ : ¬ p.Nil := by intro hn; cases hn; simp at he
      exact Finset.mem_biUnion.2 ⟨p.snd, (G.mem_neighborFinset _ _).2 (p.adj_snd hp₀),
        edges_subset_branch hp rfl (List.mem_toFinset.2 he)⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨p, hp, _⟩ := hT.existsUnique_path a u
      obtain ⟨q, hq, _⟩ := hT.existsUnique_path a v
      have hadj : G.Adj u v := by simpa using he
      have hb := (isAcyclic_iff_forall_adj_isBridge.1 hT.IsAcyclic) hadj
      have hm := (isBridge_iff_adj_and_forall_walk_mem_edges.1 hb).2 (p.reverse.append q)
      rw [edges_append, edges_reverse, List.mem_append, List.mem_reverse] at hm
      exact hm.elim (addBranch p hp) (addBranch q hq)

private theorem sum_branchEdges (hT : G.IsTree) (a : V) :
    ∑ b ∈ G.neighborFinset a, ∑ e ∈ branchEdges (G := G) a b, quadraticEdgeWeight G e =
      quadraticIrregularity G := by
  have hds : (↑(G.neighborFinset a) : Set V).PairwiseDisjoint (branchEdges (G := G) a) :=
    fun _ _ _ _ h => branchEdges_disjoint hT.IsAcyclic h
  rw [← Finset.sum_biUnion hds, union_branchEdges hT a]
  rfl

private theorem branch_weight_ge {a b : V} (hT : G.IsAcyclic) (hab : G.Adj a b) :
    (G.degree a : ℤ) ^ 2 - 1 ≤
      ∑ e ∈ branchEdges (G := G) a b, quadraticEdgeWeight G e := by
  obtain ⟨z, p, hp, hz⟩ := leaf_path_in_branch hT hab
  have h := walk_quadratic_triangle hp
  rw [hz, Nat.cast_one, one_pow] at h
  exact (le_abs_self _).trans (h.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (edges_subset_branch hp (snd_cons _ _)) (fun e _ _ => quadraticEdgeWeight_nonneg G e)))

/-- The lower estimate in `pron1`, by summing the triangle inequality
along edge-disjoint paths from a maximum-degree vertex to leaves. -/
theorem quadraticIrregularity_lower_bound (hT : G.IsTree) :
    (G.maxDegree : ℤ) * ((G.maxDegree : ℤ) ^ 2 - 1) ≤ quadraticIrregularity G := by
  letI := hT.isConnected.nonempty
  obtain ⟨a, ha⟩ := G.exists_maximal_degree_vertex
  rw [ha]
  calc
    _ = ∑ _ ∈ G.neighborFinset a, ((G.degree a : ℤ) ^ 2 - 1) := by
      simp [nsmul_eq_mul, mul_sub]
    _ ≤ ∑ b ∈ G.neighborFinset a, ∑ e ∈ branchEdges (G := G) a b, quadraticEdgeWeight G e :=
      Finset.sum_le_sum fun b hb => branch_weight_ge hT.IsAcyclic ((G.mem_neighborFinset _ _).1 hb)
    _ = _ := sum_branchEdges hT a

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem snd_append_of_not_nil {a b c : V} {p : G.Walk a b}
    (hp : ¬ p.Nil) (q : G.Walk b c) : (p.append q).snd = p.snd := by
  cases p with
  | nil => exact (hp .nil).elim
  | cons h p => rw [cons_append, snd_cons, snd_cons]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem append_path_of_distinct_branches {a b c : V}
    (hT : G.IsAcyclic) {p : G.Walk a b} {q : G.Walk b c} (hp : p.IsPath) (hq : q.IsPath)
    (hdir : p.penultimate ≠ q.snd) : (p.append q).IsPath := by
  rw [isPath_def, support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.sublist (List.tail_sublist _), ?_⟩
  intro z hzp hzq
  have hzp' : z ∈ p.reverse.support := by simpa using hzp
  have hzq' : z ∈ q.support := List.mem_of_mem_tail hzq
  have hz := vertex_common_to_branches hT hp.reverse hq (by simpa only [snd_reverse] using hdir)
    hzp' hzq'
  subst z
  have hstart : b ∉ q.support.tail := by
    have hnodup := hq.support_nodup
    rw [q.support_eq_cons, List.nodup_cons] at hnodup
    exact hnodup.1
  exact hstart hzq

omit [Fintype V] [DecidableRel G.Adj] in
private theorem edges_disjoint_of_away_from_parent {a b c : V}
    (hT : G.IsAcyclic) {p : G.Walk a b} {q : G.Walk b c} (hp : p.IsPath) (hq : q.IsPath)
    (hdir : p.penultimate ≠ q.snd) : Disjoint p.edges.toFinset q.edges.toFinset := by
  have hd := edges_disjoint_of_snd_ne hT hp.reverse hq (by simpa only [snd_reverse] using hdir)
  simpa only [edges_reverse, List.toFinset_reverse] using hd

/-- A second branching vertex gives two forward leaf paths in a single
root branch, so the triangle lower estimate for that branch is strict. -/
private theorem branch_weight_gt_of_branching {a w : V} (hT : G.IsAcyclic)
    {p : G.Walk a w} (hp : p.IsPath) (hp₀ : ¬ p.Nil) (hw : 3 ≤ G.degree w) :
    (G.degree a : ℤ) ^ 2 - 1 <
      ∑ e ∈ branchEdges (G := G) a p.snd, quadraticEdgeWeight G e := by
  classical
  have hprev : p.penultimate ∈ G.neighborFinset w :=
    (G.mem_neighborFinset _ _).2 (p.adj_penultimate hp₀).symm
  have hcard : 1 < ((G.neighborFinset w).erase p.penultimate).card := by
    rw [Finset.card_erase_of_mem hprev, G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcard
  obtain ⟨hx0, hx1⟩ := Finset.mem_erase.1 hx
  obtain ⟨hy0, hy1⟩ := Finset.mem_erase.1 hy
  have hax := (G.mem_neighborFinset _ _).1 hx1
  have hay := (G.mem_neighborFinset _ _).1 hy1
  obtain ⟨z₁, q₁, hq₁, hz₁⟩ := leaf_path_in_branch hT hax
  obtain ⟨z₂, q₂, hq₂, hz₂⟩ := leaf_path_in_branch hT hay
  let P₁ := cons hax q₁
  let P₂ := cons hay q₂
  let E := p.edges.toFinset
  let E₁ := P₁.edges.toFinset
  let E₂ := P₂.edges.toFinset
  have hd₁ : p.penultimate ≠ P₁.snd := by simpa only [P₁, snd_cons] using hx0.symm
  have hd₂ : p.penultimate ≠ P₂.snd := by simpa only [P₂, snd_cons] using hy0.symm
  have hdis₁ : Disjoint E E₁ := edges_disjoint_of_away_from_parent hT hp hq₁ hd₁
  have hdis₂ : Disjoint E E₂ := edges_disjoint_of_away_from_parent hT hp hq₂ hd₂
  have hdis₃ : Disjoint E₁ E₂ :=
    edges_disjoint_of_snd_ne hT hq₁ hq₂ (by simpa only [P₁, P₂, snd_cons] using hxy)
  have hs₁ := edges_subset_branch (append_path_of_distinct_branches hT hp hq₁ hd₁)
    (snd_append_of_not_nil hp₀ P₁)
  have hs₂ := edges_subset_branch (append_path_of_distinct_branches hT hp hq₂ hd₂)
    (snd_append_of_not_nil hp₀ P₂)
  have hsub : E ∪ E₁ ∪ E₂ ⊆ branchEdges (G := G) a p.snd := by
    intro e he
    simp only [Finset.mem_union] at he
    rcases he with h | h
    · apply hs₁
      rw [edges_append, List.mem_toFinset, List.mem_append]
      exact h.imp (fun h => List.mem_toFinset.1 h) (fun h => List.mem_toFinset.1 h)
    · apply hs₂
      rw [edges_append, List.mem_toFinset, List.mem_append]
      exact Or.inr (List.mem_toFinset.1 h)
  have ht := (le_abs_self _).trans (walk_quadratic_triangle hp)
  have ht₁ := (le_abs_self _).trans (walk_quadratic_triangle hq₁)
  have ht₂ := (le_abs_self _).trans (walk_quadratic_triangle hq₂)
  rw [hz₁, Nat.cast_one, one_pow] at ht₁
  rw [hz₂, Nat.cast_one, one_pow] at ht₂
  have hw' : (3 : ℤ) ≤ G.degree w := by exact_mod_cast hw
  calc
    _ < ((G.degree a : ℤ) ^ 2 - (G.degree w : ℤ) ^ 2) +
        ((G.degree w : ℤ) ^ 2 - 1) + ((G.degree w : ℤ) ^ 2 - 1) := by
      nlinarith [sq_nonneg ((G.degree w : ℤ) - 3)]
    _ ≤ (∑ e ∈ E, quadraticEdgeWeight G e) + (∑ e ∈ E₁, quadraticEdgeWeight G e) +
        (∑ e ∈ E₂, quadraticEdgeWeight G e) := add_le_add (add_le_add ht ht₁) ht₂
    _ = ∑ e ∈ E ∪ E₁ ∪ E₂, quadraticEdgeWeight G e := by
      rw [Finset.sum_union (Finset.disjoint_union_left.2 ⟨hdis₂, hdis₃⟩), Finset.sum_union hdis₁]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e _ _ => quadraticEdgeWeight_nonneg G e)

/-- Strictness in `pron1` when there is a branching vertex apart from
the chosen maximum-degree root. -/
theorem quadraticIrregularity_strict_of_second_branch (hT : G.IsTree)
    {a w : V} (ha : G.maxDegree = G.degree a) (haway : a ≠ w) (hw : 3 ≤ G.degree w) :
    (G.maxDegree : ℤ) * ((G.maxDegree : ℤ) ^ 2 - 1) < quadraticIrregularity G := by
  classical
  obtain ⟨p, hp, _⟩ := hT.existsUnique_path a w
  have hp₀ : ¬ p.Nil := p.not_nil_of_ne haway
  rw [ha]
  calc
    _ = ∑ _ ∈ G.neighborFinset a, ((G.degree a : ℤ) ^ 2 - 1) := by
      simp [nsmul_eq_mul, mul_sub]
    _ < ∑ b ∈ G.neighborFinset a, ∑ e ∈ branchEdges (G := G) a b, quadraticEdgeWeight G e := by
      apply Finset.sum_lt_sum (fun b hb => branch_weight_ge hT.IsAcyclic ((G.mem_neighborFinset _ _).1 hb))
      exact ⟨p.snd, (G.mem_neighborFinset _ _).2 (p.adj_snd hp₀),
        branch_weight_gt_of_branching hT.IsAcyclic hp hp₀ hw⟩
    _ = _ := sum_branchEdges hT a

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem parent_ne_next {a b c z : V} {hab : G.Adj a b} {hbc : G.Adj b c}
    {p : G.Walk c z} (hp : (cons hab (cons hbc p)).IsPath) : a ≠ c := by
  intro he
  subst c
  exact ((cons_isPath_iff _ _).1 hp).2 (by simp)

omit [DecidableEq V] in
private theorem two_le_degree {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : a ≠ c) : 2 ≤ G.degree b := by
  classical
  have hs : ({a, c} : Finset V) ⊆ G.neighborFinset b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (G.mem_neighborFinset _ _).2 hab.symm
    · exact (G.mem_neighborFinset _ _).2 hbc
  simpa [hac] using Finset.card_le_card hs

omit [DecidableEq V] in
private theorem next_eq_of_degree_le_two {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hbd : G.Adj b d)
    (hac : a ≠ c) (had : a ≠ d) (hb : G.degree b ≤ 2) : c = d := by
  classical
  by_contra hcd
  have hs : ({a, c, d} : Finset V) ⊆ G.neighborFinset b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).2 hab.symm
    · exact (G.mem_neighborFinset _ _).2 hbc
    · exact (G.mem_neighborFinset _ _).2 hbd
  have hc : 3 ≤ G.degree b := by simpa [hac, had, hcd] using Finset.card_le_card hs
  omega

/-- When the root is the only possible branching vertex, every walk in
a branch follows the same leg until it stops. -/
private theorem linear_tail_edges_subset {root a b z w : V}
    (p : G.Walk b z) (q : G.Walk b w) (hab : G.Adj a b)
    (hp : (cons hab p).IsPath) (hq : (cons hab q).IsPath)
    (hroot : root ∉ p.support) (hz : G.degree z = 1)
    (hdegree : ∀ t ≠ root, G.degree t ≤ 2) : q.edges ⊆ p.edges := by
  induction p generalizing a w with
  | nil =>
    cases q with
    | nil => exact fun _ h => h
    | cons hbc q =>
      have hc := two_le_degree hab hbc (parent_ne_next hq)
      omega
  | @cons b c z hbc p ih =>
    cases q with
    | nil => simp
    | @cons _ d w hbd q =>
      have hb : b ≠ root := fun he => hroot (he ▸ (by simp : b ∈ (cons hbc p).support))
      have he := next_eq_of_degree_le_two hab hbc hbd (parent_ne_next hp)
        (parent_ne_next hq) (hdegree b hb)
      subst d
      have hs := ih q hbc ((cons_isPath_iff _ _).1 hp).1 ((cons_isPath_iff _ _).1 hq).1
        (fun h => hroot (by simp [h])) hz
      intro e he
      simp only [edges_cons, List.mem_cons] at he ⊢
      exact he.imp id (fun h => hs h)

private theorem branchEdges_eq_leg {a b z : V} (hab : G.Adj a b) {p : G.Walk b z}
    (hp : (cons hab p).IsPath) (hz : G.degree z = 1)
    (hdegree : ∀ w ≠ a, G.degree w ≤ 2) :
    branchEdges (G := G) a b = (cons hab p).edges.toFinset := by
  classical
  refine Finset.Subset.antisymm ?_ (edges_subset_branch hp (snd_cons _ _))
  intro e he
  obtain ⟨_, w, q, hq, hqs, hqe⟩ := Finset.mem_filter.1 he
  cases q with
  | nil => simp at hqe
  | @cons _ c w hac q =>
    rw [snd_cons] at hqs
    subst c
    have hs := linear_tail_edges_subset p q hab hp hq ((cons_isPath_iff _ _).1 hp).2 hz hdegree
    rw [edges_cons, List.mem_cons] at hqe
    rw [List.mem_toFinset, edges_cons, List.mem_cons]
    exact hqe.imp id (fun h => hs h)

private theorem sum_weight_cons {a b z : V} {hab : G.Adj a b} {p : G.Walk b z}
    (hp : (cons hab p).IsPath) :
    (∑ e ∈ (cons hab p).edges.toFinset, quadraticEdgeWeight G e) =
      |(G.degree a : ℤ) ^ 2 - (G.degree b : ℤ) ^ 2| +
        ∑ e ∈ p.edges.toFinset, quadraticEdgeWeight G e := by
  have he := hp.isTrail.edges_nodup
  rw [edges_cons, List.nodup_cons] at he
  rw [edges_cons, List.toFinset_cons, Finset.sum_insert (by simpa using he.1),
    quadraticEdgeWeight_pair]

/-- On each leg, the degrees are constant at two until the final leaf.
Consequently the sum of the individual edge differences telescopes. -/
private theorem linear_tail_weight {root a b z : V} (p : G.Walk b z) (hab : G.Adj a b)
    (hp : (cons hab p).IsPath) (hroot : root ∉ p.support) (hz : G.degree z = 1)
    (hdegree : ∀ t ≠ root, G.degree t ≤ 2) :
    (∑ e ∈ p.edges.toFinset, quadraticEdgeWeight G e) = (G.degree b : ℤ) ^ 2 - 1 := by
  induction p generalizing a with
  | nil => simp [hz]
  | @cons b c z hbc p ih =>
    have hb := two_le_degree hab hbc (parent_ne_next hp)
    have hc₀ : c ≠ root := fun he => hroot (he ▸ (by simp : c ∈ (cons hbc p).support))
    have hc := hdegree c hc₀
    have hnonneg : 0 ≤ (G.degree b : ℤ) ^ 2 - (G.degree c : ℤ) ^ 2 := by
      have he : (G.degree c : ℤ) ≤ G.degree b := by exact_mod_cast hc.trans hb
      exact sub_nonneg.2 (pow_le_pow_left₀ (by positivity) he _)
    have ht := (cons_isPath_iff _ _).1 hp
    rw [sum_weight_cons ht.1, abs_of_nonneg hnonneg,
      ih hbc ht.1 (fun h => hroot (by simp [h])) hz]
    ring

/-- Equality in `pron1`: if every leg from the maximum-degree vertex
is unbranched, its edge weights telescope. -/
theorem quadraticIrregularity_eq_of_unbranched_legs (hT : G.IsTree) {a : V}
    (ha : G.maxDegree = G.degree a) (hdegree : ∀ w ≠ a, G.degree w ≤ 2) :
    quadraticIrregularity G = (G.maxDegree : ℤ) * ((G.maxDegree : ℤ) ^ 2 - 1) := by
  rw [ha, ← sum_branchEdges hT a]
  have hleg (b : V) (hb : b ∈ G.neighborFinset a) :
      (∑ e ∈ branchEdges (G := G) a b, quadraticEdgeWeight G e) = (G.degree a : ℤ) ^ 2 - 1 := by
    have hab := (G.mem_neighborFinset _ _).1 hb
    obtain ⟨z, p, hp, hz⟩ := leaf_path_in_branch hT.IsAcyclic hab
    have hnonneg : 0 ≤ (G.degree a : ℤ) ^ 2 - (G.degree b : ℤ) ^ 2 := by
      have he : (G.degree b : ℤ) ≤ G.degree a := by exact_mod_cast (ha ▸ G.degree_le_maxDegree b)
      exact sub_nonneg.2 (pow_le_pow_left₀ (by positivity) he _)
    rw [branchEdges_eq_leg hab hp hz hdegree, sum_weight_cons hp, abs_of_nonneg hnonneg,
      linear_tail_weight p hab hp ((cons_isPath_iff _ _).1 hp).2 hz hdegree]
    ring
  rw [Finset.sum_congr rfl hleg]
  simp [nsmul_eq_mul, mul_sub]

/-- Equality occurs precisely when at most one vertex has degree above two. -/
theorem quadraticIrregularity_lower_eq_iff (hT : G.IsTree) :
    quadraticIrregularity G = (G.maxDegree : ℤ) * ((G.maxDegree : ℤ) ^ 2 - 1) ↔
      ∀ a w : V, 3 ≤ G.degree a → 3 ≤ G.degree w → a = w := by
  letI := hT.isConnected.nonempty
  obtain ⟨a, ha⟩ := G.exists_maximal_degree_vertex
  constructor
  · intro he u v hu hv
    by_contra huv
    by_cases h : a = u
    · exact (quadraticIrregularity_strict_of_second_branch hT ha (h.trans_ne huv) hv).ne he.symm
    · exact (quadraticIrregularity_strict_of_second_branch hT ha h hu).ne he.symm
  · intro h
    apply quadraticIrregularity_eq_of_unbranched_legs hT ha
    intro w hw
    by_contra! hn
    have hmax := G.degree_le_maxDegree w
    rw [ha] at hmax
    exact hw (h a w (by omega) (by omega)).symm

/-- A path graph is a graph whose edges are exactly those of one simple
walk. For a tree this includes the one-vertex path. -/
def SpanningPath (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ p.edges.toFinset = G.edgeFinset

/-- A tree of maximum degree at most two consists of a single simple path. -/
theorem spanningPath_of_maxDegree_le_two (hT : G.IsTree) (hm : G.maxDegree ≤ 2) : SpanningPath G := by
  classical
  haveI := hT.isConnected.nonempty
  by_cases hE : G.edgeFinset.Nonempty
  · obtain ⟨e, he⟩ := hE
    obtain ⟨u, v, ha⟩ : ∃ u v, G.Adj u v := by
      induction e using Sym2.inductionOn with
      | _ u v => exact ⟨u, v, by simpa using he⟩
    obtain ⟨a, _, _, ha₁⟩ := leaf_path_in_branch hT.IsAcyclic ha
    obtain ⟨b, hb⟩ := Finset.card_eq_one.1 ha₁
    have hab : G.Adj a b := (G.mem_neighborFinset _ _).1 (by rw [hb]; simp)
    obtain ⟨z, p, hp, hz⟩ := leaf_path_in_branch hT.IsAcyclic hab
    refine ⟨a, z, cons hab p, hp, ?_⟩
    rw [← union_branchEdges hT a, hb, Finset.singleton_biUnion]
    exact (branchEdges_eq_leg hab hp hz (fun w _ => (G.degree_le_maxDegree w).trans hm)).symm
  · let a : V := Classical.choice (inferInstance : Nonempty V)
    exact ⟨a, a, nil, IsPath.nil, by simp [Finset.not_nonempty_iff_eq_empty.1 hE]⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem vertex_mem_support_of_incident_edge {a b v : V}
    {p : G.Walk a b} {e : Sym2 V} (hv : v ∈ e) (he : e ∈ p.edges) : v ∈ p.support := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact p.fst_mem_support_of_mem_edges he
    · exact p.snd_mem_support_of_mem_edges he

omit [Fintype V] [DecidableRel G.Adj] in
private theorem start_incidence_le_one {a b : V} {p : G.Walk a b} (hp : p.IsPath) :
    (p.edges.toFinset.filter fun e => a ∈ e).card ≤ 1 := by
  classical
  cases p with
  | nil => simp
  | cons h q =>
    have hnot := ((cons_isPath_iff _ _).1 hp).2
    have hempty : (q.edges.toFinset.filter fun e => a ∈ e) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.1
      rintro ⟨e, he⟩
      obtain ⟨he, ha⟩ := Finset.mem_filter.1 he
      exact hnot (vertex_mem_support_of_incident_edge ha (List.mem_toFinset.1 he))
    simp [edges_cons, List.toFinset_cons, Finset.filter_insert, hempty]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem incidence_along_path_le_two {a b : V} {p : G.Walk a b} (hp : p.IsPath) (x : V) :
    (p.edges.toFinset.filter fun e => x ∈ e).card ≤ 2 := by
  classical
  induction p with
  | nil => simp
  | @cons a c b h p ih =>
    by_cases hxa : x = a
    · subst x
      exact (start_incidence_le_one hp).trans (by decide)
    · have ht := ((cons_isPath_iff _ _).1 hp).1
      by_cases hxc : x = c
      · subst x
        rw [edges_cons, List.toFinset_cons, Finset.filter_insert, if_pos (Sym2.mem_iff.2 (Or.inr rfl))]
        exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (start_incidence_le_one ht))
      · have hpair : x ∉ s(a, c) := fun h => (Sym2.mem_iff.1 h).elim hxa hxc
        simpa only [edges_cons, List.toFinset_cons, Finset.filter_insert, if_neg hpair] using ih ht

theorem maxDegree_le_two_of_spanningPath (h : SpanningPath G) : G.maxDegree ≤ 2 := by
  obtain ⟨a, b, p, hp, he⟩ := h
  apply G.maxDegree_le_of_forall_degree_le
  intro v
  rw [← G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter, ← he]
  exact incidence_along_path_le_two hp v

theorem spanningPath_iff_maxDegree_le_two (hT : G.IsTree) : SpanningPath G ↔ G.maxDegree ≤ 2 :=
  ⟨maxDegree_le_two_of_spanningPath, spanningPath_of_maxDegree_le_two hT⟩

/-- The equality characterization in the form stated in `pron1`. -/
theorem quadraticIrregularity_lower_eq_iff_path_or_unique_branch (hT : G.IsTree) :
    quadraticIrregularity G = (G.maxDegree : ℤ) * ((G.maxDegree : ℤ) ^ 2 - 1) ↔
      SpanningPath G ∨ ∃! v : V, 3 ≤ G.degree v := by
  rw [quadraticIrregularity_lower_eq_iff hT, spanningPath_iff_maxDegree_le_two hT]
  constructor
  · intro h
    by_cases hm : G.maxDegree ≤ 2
    · exact Or.inl hm
    · haveI := hT.isConnected.nonempty
      obtain ⟨a, ha⟩ := G.exists_maximal_degree_vertex
      have hda : 3 ≤ G.degree a := by omega
      exact Or.inr ⟨a, hda, fun v hv => h v a hv hda⟩
  · rintro (hm | ⟨a, _, ha⟩) u v hu hv
    · have := G.degree_le_maxDegree u
      omega
    · exact (ha u hu).trans (ha v hv).symm

end Thesis.TreeIrregularity
