import Thesis.PolyominoGridContacts
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Topology.Connected.Clopen

open Set SimpleGraph

namespace Thesis.Polyomino

/-- Finite graph of surviving contacts at any stage of the full-line
cutting procedure. A diagonal contact survives when neither of the two
grid lines through its unique vertex has been removed. -/
def contactGraph (cells : List Cell) (cuts : List Line) : SimpleGraph (CellIn cells) where
  Adj p q := RemainingAdjacent cuts p q ∨ (DiagonalContact p.val q.val ∧
    .vertical (max p.val.1 q.val.1) ∉ cuts ∧ .horizontal (max p.val.2 q.val.2) ∉ cuts)
  symm := by
    rintro p q (⟨l,hs,hc⟩ | ⟨⟨hx,hy⟩,hv,hh⟩)
    · exact Or.inl ⟨l,hs.symm,hc⟩
    · exact Or.inr ⟨⟨hx.symm,hy.symm⟩,by rwa [max_comm],by rwa [max_comm]⟩
  loopless := by
    rintro p (⟨l,(hs|hs),_⟩|⟨h,_,_⟩)
    · rcases hs with ⟨e,_⟩|⟨e,_⟩ <;> obtain ⟨⟨x,y⟩,_⟩ := p <;> simp at e
    · rcases hs with ⟨e,_⟩|⟨e,_⟩ <;> obtain ⟨⟨x,y⟩,_⟩ := p <;> simp at e
    · obtain ⟨h|h,_⟩ := h <;> omega

private def forwardUncut (cuts : List Line) (p q : Cell) :=
  (q = (p.1+1,p.2) ∧ .vertical (p.1+1) ∉ cuts) ∨
  (q = (p.1,p.2+1) ∧ .horizontal (p.2+1) ∉ cuts)

instance (cells : List Cell) (cuts : List Line) : DecidableRel (contactGraph cells cuts).Adj := by
  intro p q
  have eq : RemainingAdjacent cuts p q ↔ forwardUncut cuts p.val q.val ∨ forwardUncut cuts q.val p.val := by
    unfold RemainingAdjacent SharedSide PositiveSide forwardUncut
    simp only [or_and_right,exists_or, and_assoc,exists_and_left,exists_eq_left']
    simp
  unfold contactGraph
  simp only [eq,forwardUncut]
  infer_instance

private theorem reachable_of_common_point {cells : List Cell} {cuts : List Line}
    (p q : CellIn cells) {z : Plane} (hz : z ∈ remaining cells cuts)
    (hp : z ∈ cellSquare p.val) (hq : z ∈ cellSquare q.val) : (contactGraph cells cuts).Reachable p q := by
  classical
  by_cases e : p = q
  · exact e ▸ Reachable.refl _
  apply Adj.reachable
  by_cases side : ∃ l, SharedSide p.val q.val l
  · obtain ⟨l,hs⟩ := side
    obtain ⟨a,c,rfl,he⟩ := line_at_shared_point hs hp hq
    exact Or.inl ⟨_,hs,fun hl => hz.2 a c hl he⟩
  · have diag := diagonal_of_contact_without_side (fun he => e (Subtype.ext he)) hp hq (not_exists.1 side)
    have vertex : z = contactVertex p.val q.val := by
      have hm : z ∈ cellSquare p.val ∩ cellSquare q.val := ⟨hp,hq⟩
      rwa [diagonal_square_intersection diag,mem_singleton_iff] at hm
    exact Or.inr ⟨diag,(contactVertex_survives_iff diag).1 (vertex ▸ hz)⟩

private theorem equal_components_of_reachable {cells : List Cell} {cuts : List Line} {p q : CellIn cells}
    (h : (contactGraph cells cuts).Reachable p q) :
    connectedComponentIn (remaining cells cuts) (cellCenter p.val) =
      connectedComponentIn (remaining cells cuts) (cellCenter q.val) := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail r s _ adj ih =>
    apply ih.trans
    rcases adj with ⟨l,hs,hl⟩|⟨diag,hv,hh⟩
    · exact connectedComponentIn_eq ((same_geometricPart_iff_uncut_side hs).2 hl)
    · have hz := (contactVertex_survives_iff (p:=r) (q:=s) diag).2 ⟨hv,hh⟩
      have hm : contactVertex r.val s.val ∈ cellSquare r.val ∩ cellSquare s.val := by
        rw [diagonal_square_intersection diag]; exact mem_singleton _
      exact (connectedComponentIn_eq (mem_connectedComponent_of_cellSquare r hm.1 hz)).trans
        (connectedComponentIn_eq (mem_connectedComponent_of_cellSquare s hm.2 hz)).symm

/-- At every intermediate stage, two surviving squares belong to the same
piece exactly when a path of surviving sides and corner vertices links
them. This also describes the component of every remaining point. -/
theorem in_geometric_piece_iff_reachable {cells : List Cell} {cuts : List Line} (p q : CellIn cells)
    {z : Plane} (hz : z ∈ remaining cells cuts) (hq : z ∈ cellSquare q.val) :
    z ∈ connectedComponentIn (remaining cells cuts) (cellCenter p.val) ↔ (contactGraph cells cuts).Reachable p q := by
  classical
  refine ⟨fun inC => ?_,fun path => equal_components_of_reachable path ▸ mem_connectedComponent_of_cellSquare q hq hz⟩
  haveI : Finite (CellIn cells) := finite_coe_iff.mpr cells.finite_toSet
  let C := connectedComponentIn (remaining cells cuts) (cellCenter p.val)
  let S : Set (CellIn cells) := {r | (contactGraph cells cuts).Reachable p r}
  let F (s : Set (CellIn cells)) := ⋃ r : s, cellSquare r.val.val
  have closed (s : Set (CellIn cells)) : IsClosed (F s) := isClosed_iUnion_of_finite fun r => isClosed_cellSquare r.val.val
  have sub : C ⊆ remaining cells cuts := connectedComponentIn_subset _ _
  have cover : C ⊆ F S ∪ F Sᶜ := by
    intro x hx
    obtain ⟨r,hr⟩ := (sub hx).1
    by_cases hs : r ∈ S
    · exact Or.inl (mem_iUnion.2 ⟨⟨r,hs⟩,hr⟩)
    · exact Or.inr (mem_iUnion.2 ⟨⟨r,hs⟩,hr⟩)
  have sep : C ∩ (F S ∩ F Sᶜ) = ∅ := by
    apply eq_empty_iff_forall_not_mem.2
    rintro x ⟨hx,h₁,h₂⟩
    obtain ⟨r,hr⟩ := mem_iUnion.1 h₁
    obtain ⟨s,hs⟩ := mem_iUnion.1 h₂
    exact s.property (r.property.trans (reachable_of_common_point r.val s.val (sub hx) hr hs))
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn _ _
      (closed S) (closed Sᶜ) cover sep with hl|hr
  · obtain ⟨r,hs⟩ := mem_iUnion.1 (hl inC)
    exact r.property.trans (reachable_of_common_point r.val q hz hs hq)
  · have center := cellCenter_mem_remaining cuts p
    obtain ⟨r,hs⟩ := mem_iUnion.1 (hr (mem_connectedComponentIn center))
    exact False.elim (r.property (reachable_of_common_point p r.val center (center_in_square _) hs))

theorem geometric_piece_as_union {cells : List Cell} {cuts : List Line} (p : CellIn cells) :
    connectedComponentIn (remaining cells cuts) (cellCenter p.val) =
    remaining cells cuts ∩ ⋃ q : {r : CellIn cells // (contactGraph cells cuts).Reachable p r}, cellSquare q.val.val := by
  ext z
  constructor
  · intro hz
    have rem := connectedComponentIn_subset _ _ hz
    obtain ⟨q,hq⟩ := rem.1
    exact ⟨rem,mem_iUnion.2 ⟨⟨q,(in_geometric_piece_iff_reachable p q rem hq).1 hz⟩,hq⟩⟩
  · rintro ⟨rem,union⟩
    obtain ⟨q,hq⟩ := mem_iUnion.1 union
    exact (in_geometric_piece_iff_reachable p q.val rem hq).2 q.property

end Thesis.Polyomino
