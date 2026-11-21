import Thesis.PolyominoGridContacts
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Connected.Clopen

open Set

namespace Thesis.Polyomino

private def openBox (lo hi : Cell) : Set Plane :=
  univ.pi (fun a => Ioo (axisCoord lo a : ℝ) ((axisCoord hi a : ℝ)+1))

private theorem open_box (p q : Cell) : IsOpen (openBox p q) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

private theorem connected_box (p q : Cell) : IsPreconnected (openBox p q) :=
  (convex_pi (𝕜:=ℝ) (fun _ _ => convex_Ioo _ _)).isPreconnected

private theorem closure_box (p : Cell) : closure (openBox p p) = cellSquare p := by
  unfold openBox
  rw [closure_pi_set]
  ext z
  have h (a : ℝ) : a ≠ a+1 := by linarith
  simp [cellSquare,mem_univ_pi,closure_Ioo (h _)]

private theorem center_in_box (p : Cell) : cellCenter p ∈ openBox p p := by
  intro a _
  change (axisCoord p a : ℝ) < (axisCoord p a : ℝ)+1/2 ∧
    (axisCoord p a : ℝ)+1/2 < (axisCoord p a : ℝ)+1
  constructor <;> linarith

private theorem box_subset_interior {cells : List Cell} (p : CellIn cells) :
    openBox p.val p.val ⊆ interior (remaining cells []) := by
  apply interior_maximal _ (open_box _ _)
  intro z hz
  exact ⟨⟨p,fun a => ⟨(hz a trivial).1.le,(hz a trivial).2.le⟩⟩,by simp⟩

/-- At an interior grid vertex all incident unit cells are present. This
also holds on sides and away from grid lines, for every cell containing z. -/
theorem listed_of_interior_contact {cells : List Cell} {z : Plane}
    (hz : z ∈ interior (remaining cells [])) {p : Cell} (hp : z ∈ cellSquare p) : p ∈ cells := by
  rw [← closure_box] at hp
  obtain ⟨w,hw,hw'⟩ := mem_closure_iff.1 hp _ isOpen_interior hz
  obtain ⟨q,hq⟩ := (interior_subset hw).1
  have h : q.val = p := Prod.ext (cell_coord_unique (hw' false trivial) (hq false))
    (cell_coord_unique (hw' true trivial) (hq true))
  exact h ▸ q.property

/-- If an interior point belongs to two listed cells, a side path between
them takes at most two steps, through the cell with the mixed coordinates. -/
theorem samePart_of_interior_contact {cells : List Cell} {z : Plane}
    (hz : z ∈ interior (remaining cells [])) (p q : CellIn cells)
    (hp : z ∈ cellSquare p.val) (hq : z ∈ cellSquare q.val) : SamePart [] p q := by
  let m : Cell := (q.val.1,p.val.2)
  have hm : z ∈ cellSquare m := fun a => by cases a; exact hq false; exact hp true
  let r : CellIn cells := ⟨m,listed_of_interior_contact hz hm⟩
  have hx := contact_coordinate (hp false) (hq false)
  have hy := contact_coordinate (hp true) (hq true)
  change p.val.1+1 = q.val.1 ∨ q.val.1+1 = p.val.1 ∨ p.val.1 = q.val.1 at hx
  change p.val.2+1 = q.val.2 ∨ q.val.2+1 = p.val.2 ∨ p.val.2 = q.val.2 at hy
  have hpr : SamePart [] p r := by
    rcases hx with h|h|h
    · exact .single ⟨_,Or.inl (Or.inl ⟨Prod.ext h.symm rfl,rfl⟩),by simp⟩
    · exact .single ⟨_,Or.inr (Or.inl ⟨Prod.ext h.symm rfl,rfl⟩),by simp⟩
    · have e : p = r := Subtype.ext (Prod.ext h rfl)
      exact e ▸ .refl
  apply hpr.trans
  rcases hy with h|h|h
  · exact .single ⟨_,Or.inl (Or.inr ⟨Prod.ext rfl h.symm,rfl⟩),by simp⟩
  · exact .single ⟨_,Or.inr (Or.inr ⟨Prod.ext rfl h.symm,rfl⟩),by simp⟩
  · have e : r = q := Subtype.ext (Prod.ext rfl h)
    exact e ▸ .refl

/-- A side component and its complement are finite unions of closed
squares. Their possible vertex intersections lie outside the interior. -/
theorem sideConnected_of_preconnected_interior {cells : List Cell}
    (h : IsPreconnected (interior (remaining cells []))) : SideConnected cells := by
  classical
  haveI : Finite (CellIn cells) := finite_coe_iff.mpr cells.finite_toSet
  intro p q
  let F (s : Set (CellIn cells)) := ⋃ r : s, cellSquare r.val.val
  let S : Set (CellIn cells) := {r | SamePart [] p r}
  have closed (s : Set (CellIn cells)) : IsClosed (F s) :=
    isClosed_iUnion_of_finite fun r => isClosed_cellSquare r.val.val
  have cover : interior (remaining cells []) ⊆ F S ∪ F Sᶜ := by
    intro z hz
    obtain ⟨r,hr⟩ := (interior_subset hz).1
    by_cases hs : r ∈ S
    · exact Or.inl (mem_iUnion.2 ⟨⟨r,hs⟩,hr⟩)
    · exact Or.inr (mem_iUnion.2 ⟨⟨r,hs⟩,hr⟩)
  have sep : interior (remaining cells []) ∩ (F S ∩ F Sᶜ) = ∅ := by
    apply eq_empty_iff_forall_not_mem.2
    rintro z ⟨hz,h₁,h₂⟩
    obtain ⟨r,hr⟩ := mem_iUnion.1 h₁
    obtain ⟨s,hs⟩ := mem_iUnion.1 h₂
    exact s.property (r.property.trans (samePart_of_interior_contact hz r.val s.val hr hs))
  have fromCenter (r : CellIn cells) (s : Set (CellIn cells)) (hs : cellCenter r.val ∈ F s) : r ∈ s := by
    obtain ⟨u,hu⟩ := mem_iUnion.1 hs
    have eq : u.val = r := Subtype.ext (Prod.ext
      (cell_coord_unique (center_in_box r.val false trivial) (hu false))
      (cell_coord_unique (center_in_box r.val true trivial) (hu true)))
    exact eq ▸ u.property
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 h _ _ (closed S) (closed Sᶜ) cover sep with hl|hr
  · exact fromCenter q S (hl (cellCenter_mem_interior q))
  · exact False.elim ((fromCenter p Sᶜ (hr (cellCenter_mem_interior p))) Relation.ReflTransGen.refl)

private theorem in_interior_component {cells : List Cell} (p : CellIn cells) {z : Plane}
    (hz : z ∈ interior (remaining cells [])) (hp : z ∈ cellSquare p.val) :
    z ∈ connectedComponentIn (interior (remaining cells [])) (cellCenter p.val) := by
  let U := openBox p.val p.val
  have cl : z ∈ closure U := by rwa [closure_box]
  have conn := (connected_box p.val p.val).subset_closure (subset_insert z U)
    (insert_subset cl subset_closure)
  exact conn.subset_connectedComponentIn (mem_insert_of_mem _ (center_in_box _))
    (insert_subset hz (box_subset_interior p)) (mem_insert _ _)

private theorem positive_centers {cells : List Cell} {p q : CellIn cells} {l : Line}
    (h : PositiveSide p.val q.val l) :
    connectedComponentIn (interior (remaining cells [])) (cellCenter p.val) =
    connectedComponentIn (interior (remaining cells [])) (cellCenter q.val) := by
  obtain ⟨a,_,he⟩ := positiveSide_axis h
  have ord (d : Bool) : (axisCoord p.val d : ℝ) ≤ axisCoord q.val d := by
    rw [he]; split_ifs <;> norm_num
  have sub : openBox p.val q.val ⊆ interior (remaining cells []) := by
    apply interior_maximal _ (open_box _ _)
    intro z hz
    refine ⟨?_,by simp⟩
    by_cases hc : z a ≤ (axisCoord p.val a : ℝ)+1
    · refine ⟨p,fun d => ⟨(hz d trivial).1.le,?_⟩⟩
      by_cases hd : d = a
      · exact hd ▸ hc
      · simpa [he,hd] using (hz d trivial).2.le
    · refine ⟨q,fun d => ⟨?_,(hz d trivial).2.le⟩⟩
      by_cases hd : d = a
      · subst d
        simpa [he] using (le_of_not_ge hc)
      · simpa [he,hd] using (hz d trivial).1.le
  have left : cellCenter p.val ∈ openBox p.val q.val := by
    intro d _
    exact ⟨(center_in_box p.val d trivial).1,
      (center_in_box p.val d trivial).2.trans_le (add_le_add_right (ord d) 1)⟩
  have right : cellCenter q.val ∈ openBox p.val q.val := by
    intro d _
    exact ⟨(ord d).trans_lt (center_in_box q.val d trivial).1,(center_in_box q.val d trivial).2⟩
  exact connectedComponentIn_eq ((connected_box _ _).subset_connectedComponentIn left sub right)

private theorem centers_of_side_path {cells : List Cell} {p q : CellIn cells} (path : SamePart [] p q) :
    connectedComponentIn (interior (remaining cells [])) (cellCenter p.val) =
    connectedComponentIn (interior (remaining cells [])) (cellCenter q.val) := by
  induction path with
  | refl => rfl
  | tail _ adj ih =>
    obtain ⟨_,hs,_⟩ := adj
    exact ih.trans (hs.elim positive_centers (fun h => (positive_centers h).symm))

/-- For a finite union of closed grid squares, the interior is preconnected
exactly when the cells are linked by paths of common sides. This identifies
the hypotheses under which the path argument in the proof of the minimum-dissection theorem applies. -/
theorem preconnected_interior_iff_sideConnected (cells : List Cell) :
    IsPreconnected (interior (remaining cells [])) ↔ SideConnected cells := by
  refine ⟨sideConnected_of_preconnected_interior,fun conn => ?_⟩
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  obtain ⟨p,hp⟩ := (interior_subset hx).1
  obtain ⟨q,hq⟩ := (interior_subset hy).1
  exact ⟨_,connectedComponentIn_subset _ _,in_interior_component p hx hp,
    (centers_of_side_path (conn p q)) ▸ in_interior_component q hy hq,isPreconnected_connectedComponentIn⟩

end Thesis.Polyomino
