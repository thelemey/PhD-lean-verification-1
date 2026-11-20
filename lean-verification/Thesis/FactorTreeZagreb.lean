import Thesis.FactorTreeSpecial
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open scoped BigOperators
open Thesis.ThueMorse (complexity factorLanguage factorLanguage_prefix_image)

namespace Thesis.FactorTree

/-- The sum of squared degrees over the finite factor tree. -/
noncomputable def firstZagrebOfWord (w : Nat → Bool) (n : Nat) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ∑ u ∈ factorLanguage w k, (truncatedDegree w n k u : ℤ) ^ 2

private theorem internal_square_sum (w : Nat → Bool) {n k : Nat} (h0 : 0 < k) (hk : k < n)
    (hwidth : ∀ j, complexity w j = j + 1) :
    (∑ u ∈ factorLanguage w k, (truncatedDegree w n k u : ℤ) ^ 2) =
      4 * (complexity w k : ℤ) + 5 := by
  classical
  have hcard := complexity_succ_eq_add_rightSpecials w k
  have hc : (rightSpecials w k).card = 1 := by
    rw [hwidth, hwidth] at hcard
    omega
  have hsum :
      (∑ u ∈ factorLanguage w k, (truncatedDegree w n k u : ℤ) ^ 2) =
        ∑ u ∈ factorLanguage w k, ((4 : ℤ) + 5 * if u ∈ rightSpecials w k then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [internal_degree_eq w h0 hk u hu]
    split_ifs <;> decide
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfilter : (factorLanguage w k).filter (fun u => u ∈ rightSpecials w k) =
      rightSpecials w k := by
    ext u
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp fun h => (Finset.mem_filter.1 h).1
  rw [Finset.sum_boole, hfilter, hc]
  simp [complexity, nsmul_eq_mul, mul_comm]

private theorem list_range_sum_eq (f : Nat → ℤ) (n : Nat) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- Explicit vertices of the finite factor tree, indexed by length. -/
noncomputable def factorVertices (w : Nat → Bool) (n : Nat) :
    Finset (Σ k : Nat, Fin k → Bool) :=
  (Finset.range (n + 1)).sigma (factorLanguage w)

/-- An edge is encoded by its child, with the parent level as index. -/
noncomputable def factorEdges (w : Nat → Bool) (n : Nat) :
    Finset (Σ k : Nat, Fin (k + 1) → Bool) :=
  (Finset.range n).sigma (fun k => factorLanguage w (k + 1))

theorem edge_endpoints_mem_vertices (w : Nat → Bool) (n : Nat)
    (e : Σ k : Nat, Fin (k + 1) → Bool) (he : e ∈ factorEdges w n) :
    (⟨e.1, fun i => e.2 i.castSucc⟩ : Σ k : Nat, Fin k → Bool) ∈ factorVertices w n ∧
    (⟨e.1 + 1, e.2⟩ : Σ k : Nat, Fin k → Bool) ∈ factorVertices w n := by
  rcases e with ⟨k, u⟩
  obtain ⟨hk, hu⟩ := Finset.mem_sigma.1 he
  have h : k < n := Finset.mem_range.1 hk
  constructor
  · apply Finset.mem_sigma.2
    refine ⟨Finset.mem_range.2 (by change k < n + 1; omega), ?_⟩
    rw [← factorLanguage_prefix_image w k]
    exact Finset.mem_image.2 ⟨u, hu, rfl⟩
  · exact Finset.mem_sigma.2 ⟨Finset.mem_range.2 (by change k + 1 < n + 1; omega), hu⟩

/-- The vertex and parent-edge totals in thm:factortree, for the actual
factor levels, with the Sturmian complexity as the cited input. -/
theorem factor_tree_cardinalities (w : Nat → Bool) (n : Nat) (hwidth : ∀ j, complexity w j = j + 1) :
    2 * ((factorVertices w n).card : ℤ) = ((n : ℤ) + 1) * (n + 2) ∧
    2 * ((factorEdges w n).card : ℤ) = ((n : ℤ) + 1) * (n + 2) - 2 := by
  have he := counts_of_level_width (fun k => (complexity w k : ℤ)) n
    (fun k _ => by
      change (complexity w k : ℤ) = (k : ℤ) + 1
      exact_mod_cast hwidth k)
  unfold vertexCount parentEdgeCount at he
  rw [list_range_sum_eq, list_range_sum_eq] at he
  simpa only [factorVertices, factorEdges, Finset.card_sigma, Nat.cast_sum, complexity] using he

/-- The first Zagreb index using the actual degrees of the factors
and only the classical Sturmian level widths (F1). -/
theorem firstZagrebOfWord_eq (w : Nat → Bool) {n : Nat} (hn : 0 < n)
    (hwidth : ∀ j, complexity w j = j + 1) :
    firstZagrebOfWord w n = 2 * (n : ℤ) ^ 2 + 8 * n - 4 := by
  have hverts := (counts_of_level_width (fun k => (complexity w k : ℤ)) n
    (fun k _ => by
      change (complexity w k : ℤ) = (k : ℤ) + 1
      exact_mod_cast hwidth k)).1
  unfold vertexCount at hverts
  rw [list_range_sum_eq] at hverts
  have hroot : (∑ u ∈ factorLanguage w 0, (truncatedDegree w n 0 u : ℤ) ^ 2) =
      4 * (complexity w 0 : ℤ) := by
    simp only [root_degree_eq_two w hn _ (hwidth 1), Nat.cast_ofNat]
    norm_num [complexity, nsmul_eq_mul, mul_comm]
  have hleaf : (∑ u ∈ factorLanguage w n, (truncatedDegree w n n u : ℤ) ^ 2) =
      (complexity w n : ℤ) := by
    simp [leaf_degree_eq_one w hn, complexity]
  let r := n - 1
  have hnr : n = r + 1 := by dsimp [r]; omega
  have hnSplit (f : Nat → ℤ) : (∑ k ∈ Finset.range n, f k) =
      (∑ k ∈ Finset.range r, f (k + 1)) + f 0 := by
    conv_lhs => rw [hnr, Finset.sum_range_succ']
  unfold firstZagrebOfWord
  rw [Finset.sum_range_succ, hnSplit, hroot, hleaf]
  have hinternal :
      (∑ k ∈ Finset.range r, ∑ u ∈ factorLanguage w (k + 1),
        (truncatedDegree w n (k + 1) u : ℤ) ^ 2) =
      ∑ k ∈ Finset.range r, (4 * (complexity w (k + 1) : ℤ) + 5) := by
    apply Finset.sum_congr rfl
    intro k hk
    have h := Finset.mem_range.1 hk
    exact internal_square_sum w (by omega) (by omega) hwidth
  rw [hinternal, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.sum_range_succ, hnSplit] at hverts
  have hc : (complexity w n : ℤ) = (n : ℤ) + 1 := by exact_mod_cast hwidth n
  have hr : (r : ℤ) = (n : ℤ) - 1 := by dsimp [r]; omega
  rw [hc] at hverts ⊢
  rw [hr]
  ring_nf at hverts ⊢
  omega

end Thesis.FactorTree
