import Thesis.FactorTreeIncidence

open scoped BigOperators
open Thesis.ThueMorse (complexity factorLanguage)

namespace Thesis.FactorTree

/-- An edge is oriented from its shorter factor to its longer factor. -/
noncomputable def edgeDegrees (w : Nat → Bool) (n : Nat) (e : Σ k : Nat, Fin (k + 1) → Bool) :
    Nat × Nat :=
  (truncatedDegree w n e.1 (wordPrefix e.2), truncatedDegree w n (e.1 + 1) e.2)

noncomputable def edgeDegreeCount (w : Nat → Bool) (n p c : Nat) : ℤ :=
  ((factorEdges w n).filter (fun e => edgeDegrees w n e = (p, c))).card

private theorem card_filter_factorEdges (w : Nat → Bool) (n : Nat)
    (P : (Σ k : Nat, Fin (k + 1) → Bool) → Prop) [DecidablePred P] :
    ((factorEdges w n).filter P).card =
      ∑ k ∈ Finset.range n, ((factorLanguage w (k + 1)).filter
        (fun v => P ⟨k, v⟩)).card := by
  have he : (factorEdges w n).filter P = (Finset.range n).sigma
      (fun k => (factorLanguage w (k + 1)).filter (fun v => P ⟨k, v⟩)) := by
    ext ⟨k, v⟩
    simp [factorEdges, and_assoc]
  rw [he, Finset.card_sigma]

theorem edgeDegrees_parent_cases (w : Nat → Bool) {n : Nat}
    (hwidth : ∀ j, complexity w j = j + 1)
    {e : Σ k : Nat, Fin (k + 1) → Bool} (he : e ∈ factorEdges w n) :
    (edgeDegrees w n e).1 = 2 ∨ (edgeDegrees w n e).1 = 3 := by
  rcases e with ⟨k, v⟩
  obtain ⟨hk, hv⟩ := Finset.mem_sigma.1 he
  have hk' := Finset.mem_range.1 hk
  change truncatedDegree w n k (wordPrefix v) = 2 ∨ truncatedDegree w n k (wordPrefix v) = 3
  by_cases h0 : k = 0
  · subst k
    exact Or.inl (root_degree_eq_two w hk' _ (hwidth 1))
  · rw [internal_degree_eq w (Nat.pos_of_ne_zero h0) hk' _ (parent_factor w k hv)]
    split_ifs <;> simp

theorem edgeDegrees_child_cases (w : Nat → Bool) {n : Nat}
    {e : Σ k : Nat, Fin (k + 1) → Bool} (he : e ∈ factorEdges w n) :
    (edgeDegrees w n e).2 = 1 ∨ (edgeDegrees w n e).2 = 2 ∨ (edgeDegrees w n e).2 = 3 := by
  rcases e with ⟨k, v⟩
  obtain ⟨hk, hv⟩ := Finset.mem_sigma.1 he
  have hk' := Finset.mem_range.1 hk
  change truncatedDegree w n (k + 1) v = 1 ∨ truncatedDegree w n (k + 1) v = 2 ∨
    truncatedDegree w n (k + 1) v = 3
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hk') with heq | hlt
  · subst n
    exact Or.inl (leaf_degree_eq_one w (Nat.succ_pos _) _)
  · rw [internal_degree_eq w (Nat.succ_pos _) hlt _ hv]
    split_ifs <;> simp

/-- The two outgoing edges from the last internal special vertex are
all the edges with degrees (3,1). -/
theorem edgeDegreeCount_three_one (w : Nat → Bool) {n : Nat} (hn : 2 ≤ n)
    (hwidth : ∀ j, complexity w j = j + 1) :
    edgeDegreeCount w n 3 1 = 2 := by
  unfold edgeDegreeCount
  rw [card_filter_factorEdges]
  have hn' : n - 1 + 1 = n := by omega
  rw [show Finset.range n = Finset.range (n - 1 + 1) by rw [hn'], Finset.sum_range_succ]
  have hlast :
      ((factorLanguage w (n - 1 + 1)).filter (fun v => edgeDegrees w n ⟨n - 1, v⟩ =
        (3, 1))).card = 2 := by
    simp only [edgeDegrees, Prod.mk.injEq]
    exact (congrArg (fun height => ((factorLanguage w (n - 1 + 1)).filter (fun v =>
      truncatedDegree w height (n - 1) (wordPrefix v) = 3 ∧
      truncatedDegree w height (n - 1 + 1) v = 1)).card) hn'.symm).trans
        (last_level_three_one_edges w (n - 1) (by omega) hwidth)
  rw [hlast]
  have hrest :
      (∑ k ∈ Finset.range (n - 1),
        ((factorLanguage w (k + 1)).filter (fun v => edgeDegrees w n ⟨k, v⟩ =
          (3, 1))).card) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.1 hk
    apply Finset.card_eq_zero.2
    apply Finset.eq_empty_iff_forall_not_mem.2
    intro v hv
    obtain ⟨hm, hd⟩ := Finset.mem_filter.1 hv
    have hc := congrArg Prod.snd hd
    change truncatedDegree w n (k + 1) v = 1 at hc
    rw [internal_degree_eq w (Nat.succ_pos _) (by omega) _ hm] at hc
    split_ifs at hc <;> omega
  simp [hrest]

private theorem card_special_extensions (w : Nat → Bool) (k : Nat)
    (hwidth : ∀ j, complexity w j = j + 1) :
    ((factorLanguage w (k + 1)).filter
      (fun v => wordPrefix v ∈ rightSpecials w k ∧ v ∈ rightSpecials w (k + 1))).card =
      (by classical exact if specialEdgeAt w k then 1 else 0) := by
  classical
  obtain ⟨u, hu, huUnique⟩ := unique_right_special_of_complexity w (k + 1) (hwidth _) (hwidth _)
  have hiff : ∀ v, v ∈ rightSpecials w (k + 1) ↔ v = u :=
    fun v => ⟨fun hv => huUnique v hv, fun h => h ▸ hu⟩
  rw [show specialEdgeAt w k ↔ wordPrefix u ∈ rightSpecials w k by
    constructor
    · rintro ⟨v, hv, hp⟩
      rwa [(hiff v).1 hv] at hp
    · exact fun hp => ⟨u, hu, hp⟩]
  have he :
      ((factorLanguage w (k + 1)).filter
        (fun v => wordPrefix v ∈ rightSpecials w k ∧ v ∈ rightSpecials w (k + 1))) =
      ({u} : Finset (Fin (k + 1) → Bool)).filter (fun v => wordPrefix v ∈ rightSpecials w k) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hp, hv⟩
      exact ⟨(hiff v).1 hv, hp⟩
    · rintro ⟨rfl, hp⟩
      exact ⟨(Finset.mem_filter.1 hu).1, hp, hu⟩
  rw [he, Finset.filter_singleton]
  by_cases hp : wordPrefix u ∈ rightSpecials w k <;> simp [hp]

/-- The edges joining degree-three vertices occur exactly once per level
inside the initial constant run, starting above the root. -/
theorem edgeDegreeCount_three_three (w : Nat → Bool) {d n : Nat} (hd : 0 < d) (hn : d + 2 ≤ n)
    (x : Bool) (hrun : ∀ i < d, w i = x) (hchange : w d ≠ x)
    (hwidth : ∀ j, complexity w j = j + 1)
    (hreversal : ∀ j (u : Fin j → Bool), u ∈ rightSpecials w j →
      List.ofFn u = reversedPrefix w j) :
    edgeDegreeCount w n 3 3 = (d : ℤ) - 1 := by
  classical
  unfold edgeDegreeCount
  rw [card_filter_factorEdges]
  have hcount :
      (∑ k ∈ Finset.range n,
        ((factorLanguage w (k + 1)).filter (fun v => edgeDegrees w n ⟨k, v⟩ =
          (3, 3))).card) =
      ∑ k ∈ Finset.range n, if 0 < k ∧ k < d then (1 : Nat) else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn := Finset.mem_range.1 hk
    by_cases hroot : k = 0
    · subst k
      simp [edgeDegrees, root_degree_eq_two w hkn _ (hwidth 1)]
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hkn) with hlast | hi
    · subst n
      have hkd : ¬ k < d := by omega
      simp [edgeDegrees, leaf_degree_eq_one w (Nat.succ_pos _), hkd]
    · have he :
          ((factorLanguage w (k + 1)).filter (fun v => edgeDegrees w n ⟨k, v⟩ = (3, 3))) =
          ((factorLanguage w (k + 1)).filter
            (fun v => wordPrefix v ∈ rightSpecials w k ∧ v ∈ rightSpecials w (k + 1))) := by
        ext v
        simp only [Finset.mem_filter, edgeDegrees, Prod.mk.injEq]
        refine and_congr_right fun hv => ?_
        rw [internal_degree_eq w (Nat.pos_of_ne_zero hroot) hkn _ (parent_factor w k hv),
          internal_degree_eq w (Nat.succ_pos _) hi _ hv]
        by_cases hp : wordPrefix v ∈ rightSpecials w k <;>
          by_cases hc : v ∈ rightSpecials w (k + 1) <;> simp [hp, hc]
      rw [he, card_special_extensions w k hwidth]
      rw [specialEdgeAt_iff_reversed_prefix w k hwidth hreversal,
        reversedPrefixes_adjacent_iff w hd x hrun hchange]
      simp [Nat.pos_of_ne_zero hroot]
  rw [hcount, Finset.sum_boole]
  have he : (Finset.range n).filter (fun k => 0 < k ∧ k < d) = (Finset.range d).erase 0 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    omega
  rw [he]
  have hc := Finset.card_erase_of_mem (s := Finset.range d) (Finset.mem_range.2 hd)
  rw [hc, Finset.card_range]
  change ((d - 1 : Nat) : ℤ) = (d : ℤ) - 1
  exact Nat.cast_sub hd

theorem edgeDegreeCount_eq_sum (w : Nat → Bool) (n p c : Nat) :
    edgeDegreeCount w n p c =
      ∑ e ∈ factorEdges w n, if edgeDegrees w n e = (p, c) then (1 : ℤ) else 0 :=
  Finset.natCast_card_filter _ _

/-- Sum of any weight given by the endpoint degrees, using the six
possible oriented degree pairs. -/
theorem sum_edgeDegrees_eq (w : Nat → Bool) (n : Nat)
    (hwidth : ∀ j, complexity w j = j + 1) (weight : Nat × Nat → ℤ) :
    (∑ e ∈ factorEdges w n, weight (edgeDegrees w n e)) =
      weight (2, 1) * edgeDegreeCount w n 2 1 +
      weight (3, 1) * edgeDegreeCount w n 3 1 +
      weight (2, 2) * edgeDegreeCount w n 2 2 +
      weight (2, 3) * edgeDegreeCount w n 2 3 +
      weight (3, 2) * edgeDegreeCount w n 3 2 +
      weight (3, 3) * edgeDegreeCount w n 3 3 := by
  simp only [edgeDegreeCount_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rcases edgeDegrees_parent_cases w hwidth he with hp | hp <;>
    rcases edgeDegrees_child_cases w he with hc | hc | hc <;>
    rw [show edgeDegrees w n e = (_, _) from Prod.ext hp hc] <;> simp

theorem sum_indicator_parent_degree (w : Nat → Bool) (n d : Nat) :
    (∑ e ∈ factorEdges w n, if (edgeDegrees w n e).1 = d then (1 : ℤ) else 0) =
      (parentEnds w n d : ℤ) := by
  rw [Finset.sum_boole, card_filter_factorEdges]
  simp only [parentEnds, edgeDegrees]

theorem sum_indicator_child_degree (w : Nat → Bool) (n d : Nat) :
    (∑ e ∈ factorEdges w n, if (edgeDegrees w n e).2 = d then (1 : ℤ) else 0) =
      (childEnds w n d : ℤ) := by
  rw [Finset.sum_boole, card_filter_factorEdges]
  simp only [childEnds, edgeDegrees]

end Thesis.FactorTree
