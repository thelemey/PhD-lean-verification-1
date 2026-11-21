import Thesis.FactorTreeGraph
import Thesis.TreeIrregularity
import Thesis.SturmianFactorTree

open scoped BigOperators

namespace Thesis.FactorTree

/-- The degree used in the source's count agrees with SimpleGraph.degree. -/
theorem factorGraph_degree {w : Nat → Bool} {n : Nat} (v : FactorVertex w n) :
    (factorGraph w n).degree v = truncatedDegree w n v.val.1 v.val.2 := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.incidenceFinset_eq_filter,
    factorGraph_edgeFinset, Finset.filter_image,
    Finset.card_image_of_injective _ graphEdge_injective]
  have hfilter :
      ((factorEdges w n).attach.filter fun e => v ∈ graphEdge e) =
        (factorEdges w n).attach.filter (fun e =>
          factorEdgeChild e.val = v.val ∨ factorEdgeParent e.val = v.val) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_attach, true_and, graphEdge, Sym2.mem_iff]
    simp only [Subtype.ext_iff, parentVertex, childVertex, or_comm, eq_comm]
  rw [hfilter, Finset.filter_attach (fun e =>
    factorEdgeChild e = v.val ∨ factorEdgeParent e = v.val) (factorEdges w n),
    Finset.card_map, Finset.card_attach]
  exact (truncatedDegree_eq_card_incident _ _ _ _ v.property).symm

/-- The first Zagreb index as a sum of squared SimpleGraph degrees. -/
noncomputable def graphFirstZagreb (w : Nat → Bool) (n : Nat) : ℤ :=
  ∑ v : FactorVertex w n, ((factorGraph w n).degree v : ℤ) ^ 2

theorem graphFirstZagreb_eq (w : Nat → Bool) (n : Nat) :
    graphFirstZagreb w n = firstZagrebOfWord w n := by
  unfold graphFirstZagreb firstZagrebOfWord
  simp_rw [factorGraph_degree]
  rw [Finset.univ_eq_attach, Finset.sum_attach (factorVertices w n)
    (fun x => (truncatedDegree w n x.1 x.2 : ℤ) ^ 2)]
  exact Finset.sum_sigma _ _ _

/-- A sum over the actual undirected edges using a symmetric function of
their endpoint degrees. -/
noncomputable def graphEdgeDegreeSum (w : Nat → Bool) (n : Nat)
    (weight : {f : Nat → Nat → ℤ // ∀ p c, f p c = f c p}) : ℤ :=
  ∑ e ∈ (factorGraph w n).edgeFinset,
    Sym2.lift ⟨fun u v => weight.val ((factorGraph w n).degree u) ((factorGraph w n).degree v),
      fun _ _ => weight.property _ _⟩ e

theorem graphEdgeDegreeSum_eq (w : Nat → Bool) (n : Nat)
    (weight : {f : Nat → Nat → ℤ // ∀ p c, f p c = f c p}) :
    graphEdgeDegreeSum w n weight =
      ∑ e ∈ factorEdges w n, weight.val (edgeDegrees w n e).1 (edgeDegrees w n e).2 := by
  classical
  unfold graphEdgeDegreeSum
  rw [factorGraph_edgeFinset, Finset.sum_image]
  · simp only [graphEdge, Sym2.lift_mk, factorGraph_degree]
    exact Finset.sum_attach (factorEdges w n)
      (fun e => weight.val (edgeDegrees w n e).1 (edgeDegrees w n e).2)
  · exact fun _ _ _ _ h => graphEdge_injective h

noncomputable def graphAlbertson (w : Nat → Bool) (n : Nat) : ℤ :=
  graphEdgeDegreeSum w n ⟨fun p c => |(p : ℤ) - c|, fun _ _ => abs_sub_comm _ _⟩

noncomputable def graphQuadraticAlbertson (w : Nat → Bool) (n : Nat) : ℤ :=
  TreeIrregularity.quadraticIrregularity (factorGraph w n)

private theorem graphQuadraticAlbertson_eq_edgeDegreeSum (w : Nat → Bool) (n : Nat) :
    graphQuadraticAlbertson w n =
      graphEdgeDegreeSum w n ⟨fun p c => |(p : ℤ) ^ 2 - (c : ℤ) ^ 2|, fun _ _ => abs_sub_comm _ _⟩ :=
  rfl

noncomputable def graphSecondZagreb (w : Nat → Bool) (n : Nat) : ℤ :=
  graphEdgeDegreeSum w n ⟨fun p c => (p : ℤ) * c, fun _ _ => mul_comm _ _⟩

/-- The full defense statement for a characteristic Sturmian word as
formulas for the vertices and degrees of its finite undirected tree. -/
theorem characteristic_factorGraph_indices {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a)
    {d n : Nat} (hd : 0 < d) (hn : d + 2 ≤ n) (x : Bool)
    (hrun : ∀ i < d, characteristicWord a i = x) (hchange : characteristicWord a d ≠ x) :
    let w := characteristicWord a
    (factorGraph w n).IsTree ∧
    Fintype.card (FactorVertex w n) = (n + 1) * (n + 2) / 2 ∧
    graphAlbertson w n = 4 * (n : ℤ) - 2 * d ∧
    graphQuadraticAlbertson w n = 18 * (n : ℤ) - 10 * d - 2 ∧
    graphFirstZagreb w n = 2 * (n : ℤ) ^ 2 + 8 * n - 4 ∧
    graphSecondZagreb w n = 2 * (n : ℤ) ^ 2 + 10 * n - 11 + d := by
  intro w
  refine ⟨factorGraph_isTree w n, ?_⟩
  rw [Fintype.card_coe, graphFirstZagreb_eq, graphAlbertson,
    graphQuadraticAlbertson_eq_edgeDegreeSum,
    graphSecondZagreb, graphEdgeDegreeSum_eq, graphEdgeDegreeSum_eq, graphEdgeDegreeSum_eq]
  exact characteristic_factor_tree_indices ha ha' hirr hd hn x hrun hchange

end Thesis.FactorTree
