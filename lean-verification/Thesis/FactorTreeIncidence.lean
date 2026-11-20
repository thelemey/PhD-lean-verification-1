import Thesis.FactorTreeZagreb

open scoped BigOperators
open Thesis.ThueMorse (complexity factorLanguage factorLanguage_prefix_image)

namespace Thesis.FactorTree

/-- Count edge endpoints satisfying a condition on the parent or child
degree. Each edge is enumerated by its child in the next level. -/
noncomputable def parentEnds (w : Nat → Bool) (n d : Nat) : Nat :=
  ∑ k ∈ Finset.range n,
    ((factorLanguage w (k + 1)).filter (fun v => truncatedDegree w n k (wordPrefix v) = d)).card

noncomputable def childEnds (w : Nat → Bool) (n d : Nat) : Nat :=
  ∑ k ∈ Finset.range n,
    ((factorLanguage w (k + 1)).filter (fun v => truncatedDegree w n (k + 1) v = d)).card

private theorem parent_factor (w : Nat → Bool) (k : Nat) {v : Fin (k + 1) → Bool}
    (h : v ∈ factorLanguage w (k + 1)) : wordPrefix v ∈ factorLanguage w k := by
  rw [← factorLanguage_prefix_image w k]
  exact Finset.mem_image.2 ⟨v, h, rfl⟩

private theorem special_card_one (w : Nat → Bool) (k : Nat)
    (hwidth : ∀ j, complexity w j = j + 1) : (rightSpecials w k).card = 1 := by
  have h := complexity_succ_eq_add_rightSpecials w k
  rw [hwidth, hwidth] at h
  omega

private theorem parentEnds_three (w : Nat → Bool) {n : Nat} (hn : 0 < n)
    (hwidth : ∀ j, complexity w j = j + 1) : parentEnds w n 3 = 2 * (n - 1) := by
  unfold parentEnds
  have he :
      (∑ k ∈ Finset.range n,
        ((factorLanguage w (k + 1)).filter (fun v => truncatedDegree w n k (wordPrefix v) = 3)).card)
        = ∑ k ∈ Finset.range n, if k = 0 then 0 else 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.1 hk
    by_cases h0 : k = 0
    · subst k
      simp [root_degree_eq_two w hn _ (hwidth 1)]
    · rw [if_neg h0, ← edges_from_special_card w k (hwidth _) (hwidth _)]
      congr 1
      ext v
      simp only [Finset.mem_filter]
      refine and_congr_right fun hv => ?_
      rw [internal_degree_eq w (Nat.pos_of_ne_zero h0) hk' _ (parent_factor w k hv)]
      split_ifs <;> simp_all
  rw [he]
  have hn' : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn', Finset.sum_range_succ']
  simp [Nat.mul_comm]

private theorem childEnds_three (w : Nat → Bool) {n : Nat} (hn : 0 < n)
    (hwidth : ∀ j, complexity w j = j + 1) : childEnds w n 3 = n - 1 := by
  unfold childEnds
  have hn' : n = (n - 1) + 1 := by omega
  rw [show Finset.range n = Finset.range (n - 1 + 1) by rw [← hn'], Finset.sum_range_succ]
  have hlast :
      ((factorLanguage w (n - 1 + 1)).filter
        (fun v => truncatedDegree w n (n - 1 + 1) v = 3)).card = 0 := by
    have hh : n - 1 + 1 = n := by omega
    rw [hh]
    simp [leaf_degree_eq_one w hn]
  rw [hlast, Nat.add_zero]
  calc
    _ = ∑ k ∈ Finset.range (n - 1), (1 : Nat) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have hfilter :
          ((factorLanguage w (k + 1)).filter (fun v => truncatedDegree w n (k + 1) v = 3)) =
            rightSpecials w (k + 1) := by
        ext v
        simp only [rightSpecials, Finset.mem_filter]
        refine and_congr_right fun hv => ?_
        rw [internal_degree_eq w (Nat.succ_pos _) (by omega) _ hv]
        simp only [rightSpecials, Finset.mem_filter, hv, true_and]
        by_cases hs : v ∈ rightSpecials w (k + 1)
        · have hs' : (children w (k + 1) v).card = 2 := (Finset.mem_filter.mp hs).2
          simp [hs']
        · have hs' : (children w (k + 1) v).card ≠ 2 :=
            fun h => hs (Finset.mem_filter.mpr ⟨hv, h⟩)
          simp [hs']
      rw [hfilter, special_card_one w (k + 1) hwidth]
    _ = _ := by simp

/-- Each of the n−1 internal right-special vertices contributes one
incoming and two outgoing edge incidences. -/
theorem degree_three_incidence (w : Nat → Bool) {n : Nat} (hn : 0 < n)
    (hwidth : ∀ j, complexity w j = j + 1) :
    parentEnds w n 3 + childEnds w n 3 = 3 * (n - 1) := by
  rw [parentEnds_three w hn hwidth, childEnds_three w hn hwidth]
  omega

/-- Each leaf is the child of exactly one parent edge. -/
theorem leaf_incidence (w : Nat → Bool) {n : Nat} (hn : 0 < n)
    (hwidth : ∀ j, complexity w j = j + 1) :
    childEnds w n 1 = n + 1 := by
  unfold childEnds
  have hn' : n = (n - 1) + 1 := by omega
  rw [show Finset.range n = Finset.range (n - 1 + 1) by rw [← hn'], Finset.sum_range_succ]
  have hlast :
      ((factorLanguage w (n - 1 + 1)).filter
        (fun v => truncatedDegree w n (n - 1 + 1) v = 1)).card = n + 1 := by
    have hh : n - 1 + 1 = n := by omega
    rw [hh]
    simpa [leaf_degree_eq_one w hn, complexity] using hwidth n
  rw [hlast]
  suffices h :
      (∑ k ∈ Finset.range (n - 1),
        ((factorLanguage w (k + 1)).filter (fun v => truncatedDegree w n (k + 1) v = 1)).card)
        = 0 by simp [h]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_range.1 hk
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_iff_forall_not_mem.2
  intro v hv
  obtain ⟨hv', hd⟩ := Finset.mem_filter.1 hv
  rw [internal_degree_eq w (Nat.succ_pos _) (by omega) _ hv'] at hd
  split_ifs at hd <;> omega

/-- There are two edges of type (3,1) at the final level. -/
theorem last_level_three_one_edges (w : Nat → Bool) (k : Nat) (hk : 0 < k)
    (hwidth : ∀ j, complexity w j = j + 1) :
    ((factorLanguage w (k + 1)).filter (fun v =>
      truncatedDegree w (k + 1) k (wordPrefix v) = 3 ∧
      truncatedDegree w (k + 1) (k + 1) v = 1)).card = 2 := by
  rw [← edges_from_special_card w k (hwidth _) (hwidth _)]
  congr 1
  ext v
  simp only [Finset.mem_filter, leaf_degree_eq_one w (Nat.succ_pos _), and_true]
  refine and_congr_right fun hv => ?_
  rw [internal_degree_eq w hk (Nat.lt_succ_self _) _ (parent_factor w k hv)]
  split_ifs <;> simp_all

end Thesis.FactorTree
