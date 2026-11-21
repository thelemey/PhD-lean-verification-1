import Thesis.PolyominoInterior

open Set

namespace Thesis.Polyomino

theorem isClosed_cellSquare (p : Cell) : IsClosed (cellSquare p) := by
  have he : cellSquare p = ⋂ a : Bool, (fun z : Plane => z a) ⁻¹'
      Icc (axisCoord p a : ℝ) ((axisCoord p a : ℝ)+1) := by
    ext
    simp [cellSquare]
  rw [he]
  exact isClosed_iInter fun a => isClosed_Icc.preimage (continuous_apply a)

theorem center_in_square (p : Cell) : cellCenter p ∈ cellSquare p := by
  intro a
  simp only [cellCenter, mem_Icc]
  constructor <;> linarith

/-- For any finite union of closed squares, including ones meeting only at
vertices, the pieces are individual squares exactly when every surviving
point belongs to a unique original square. -/
theorem geometricallySeparated_iff_unique_square {cells : List Cell} {cuts : List Line} :
    GeometricallySeparated cells cuts ↔
      ∀ (p q : CellIn cells) (z : Plane), z ∈ remaining cells cuts →
        z ∈ cellSquare p.val → z ∈ cellSquare q.val → p = q := by
  classical
  constructor
  · intro h p q z hz hp hq
    have cp := mem_connectedComponent_of_cellSquare p hp hz
    have cq := mem_connectedComponent_of_cellSquare q hq hz
    apply h
    rw [(connectedComponentIn_eq cp).trans (connectedComponentIn_eq cq).symm]
    exact mem_connectedComponentIn (cellCenter_mem_remaining cuts q)
  · intro unique p q hq
    by_contra hne
    haveI : Finite (CellIn cells) := finite_coe_iff.mpr cells.finite_toSet
    let others := ⋃ r : {i : CellIn cells // i ≠ p}, cellSquare r.val.val
    have hclosed : IsClosed others := isClosed_iUnion_of_finite fun r => isClosed_cellSquare r.val.val
    let C := connectedComponentIn (remaining cells cuts) (cellCenter p.val)
    have hC : IsPreconnected C := isPreconnected_connectedComponentIn
    have hsub : C ⊆ remaining cells cuts := connectedComponentIn_subset _ _
    have alone {z : Plane} (hz : z ∈ remaining cells cuts) (hp : z ∈ cellSquare p.val) :
        z ∉ others := by
      intro ho
      obtain ⟨r, hr⟩ := mem_iUnion.1 ho
      exact r.property (unique _ _ _ hz hr hp)
    have covered : C ⊆ othersᶜ ∪ (cellSquare p.val)ᶜ := by
      intro z hz
      by_cases hp : z ∈ cellSquare p.val
      · exact Or.inl (alone (hsub hz) hp)
      · exact Or.inr hp
    have hp := cellCenter_mem_remaining cuts p
    have hq' := cellCenter_mem_remaining cuts q
    obtain ⟨z, hz, hno, hnp⟩ := hC _ _ hclosed.isOpen_compl (isClosed_cellSquare _).isOpen_compl
      covered ⟨_, mem_connectedComponentIn hp, alone hp (center_in_square _)⟩
      ⟨_, hq, fun h => hne (unique _ _ _ hq' h (center_in_square _))⟩
    obtain ⟨r, hr⟩ := (hsub hz).1
    by_cases h : r = p
    · exact hnp (h ▸ hr)
    · exact hno (mem_iUnion.2 ⟨⟨r, h⟩, hr⟩)

theorem line_at_shared_point {p q : Cell} {l : Line} (h : SharedSide p q l)
    {z : Plane} (hp : z ∈ cellSquare p) (hq : z ∈ cellSquare q) :
    ∃ a c, l = axisLine a c ∧ z a = (c : ℝ) := by
  have forward {u v : Cell} (hu : z ∈ cellSquare u) (hv : z ∈ cellSquare v)
      (hs : PositiveSide u v l) : ∃ a c, l = axisLine a c ∧ z a = (c : ℝ) := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨false, u.1 + 1, rfl, ?_⟩
      exact le_antisymm (by simpa [axisCoord] using (hu false).2) (hv false).1
    · refine ⟨true, u.2 + 1, rfl, ?_⟩
      exact le_antisymm (by simpa [axisCoord] using (hu true).2) (hv true).1
  exact h.elim (forward hp hq) (forward hq hp)

/-- A precise check on the sufficiency argument in §4.2. Cutting all internal
sides suffices exactly when no contact between distinct, non-side-adjacent
squares survives. Such contacts can occur at grid vertices. -/
theorem geometricallySeparated_iff_sides_and_contacts {cells : List Cell} {cuts : List Line} :
    GeometricallySeparated cells cuts ↔ Separates cells cuts ∧
      ∀ (p q : CellIn cells), p ≠ q → (∀ l, ¬ SharedSide p.val q.val l) →
        ∀ z ∈ cellSquare p.val ∩ cellSquare q.val, z ∉ remaining cells cuts := by
  constructor
  · intro h
    exact ⟨separates_of_geometricallySeparated h, fun p q hne _ z hz hr =>
      hne (geometricallySeparated_iff_unique_square.1 h p q z hr hz.1 hz.2)⟩
  · rintro ⟨hs, hc⟩
    apply geometricallySeparated_iff_unique_square.2
    intro p q z hz hp hq
    by_contra hne
    by_cases side : ∃ l, SharedSide p.val q.val l
    · obtain ⟨l, hl⟩ := side
      obtain ⟨a, c, he, hez⟩ := line_at_shared_point hl hp hq
      exact hz.2 a c (he ▸ cut_of_sharedSide hs hl) hez
    · exact hc p q hne (fun l hl => side ⟨l, hl⟩) z ⟨hp,hq⟩ hz

/-- The source's line count is attained precisely when its proposed family
of cuts separates the actual geometric union. Any family of that cardinality
must contain the same lines, since every internal side is mandatory. -/
theorem line_count_attained_iff (cells : List Cell) :
    (∃ cuts, GeometricallySeparated cells cuts ∧ cuts.length = (internalLines cells).length) ↔
      GeometricallySeparated cells (internalLines cells) := by
  constructor
  · rintro ⟨cuts, h, he⟩
    have hsub := (separates_iff _ _).1 (separates_of_geometricallySeparated h)
    have same (l : Line) : l ∈ cuts ↔ l ∈ internalLines cells := by
      refine ⟨?_, hsub l⟩
      intro hl
      by_contra hnot
      have hn : (l :: internalLines cells).Nodup := List.nodup_cons.2 ⟨hnot, internalLines_nodup _⟩
      have hle := FiniteList.nodup_length_le_of_subset hn (ys := cuts) (by
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj
        · exact hl
        · exact hsub j hj)
      simp only [List.length_cons] at hle
      omega
    have hr : remaining cells cuts = remaining cells (internalLines cells) := by
      ext z
      simp only [remaining, mem_setOf_eq, same]
    simpa only [GeometricallySeparated, hr] using h
  · exact fun h => ⟨_, h, rfl⟩

/-- In the corner-contact example one cut really suffices, while the empty
family fails. Thus the geometric minimum is 1 and the internal-line count is 0. -/
theorem corner_contact_minimum_one :
    let cells : List Cell := [(0,0),(1,1)]
    internalLines cells = [] ∧ GeometricallySeparated cells [.vertical 1] ∧
      ∀ cuts, GeometricallySeparated cells cuts → 1 ≤ cuts.length := by
  dsimp only
  refine ⟨by decide, ?_, ?_⟩
  · apply geometricallySeparated_iff_unique_square.2
    intro p q z hz hp hq
    have cases' (r : CellIn [(0,0),(1,1)]) : r.val = (0,0) ∨ r.val = (1,1) := by
      simpa using r.property
    have onLine {u v : Cell} (hu : u = (0,0)) (hv : v = (1,1))
        (hzu : z ∈ cellSquare u) (hzv : z ∈ cellSquare v) : False := by
      subst u v
      have hlow := (hzv false).1
      have hhigh := (hzu false).2
      norm_num [axisCoord] at hlow hhigh
      exact hz.2 false 1 (by decide) (by norm_num; linarith)
    rcases cases' p with hp' | hp' <;> rcases cases' q with hq' | hq'
    · exact Subtype.ext (hp'.trans hq'.symm)
    · exact (onLine hp' hq' hp hq).elim
    · exact (onLine hq' hp' hq hp).elim
    · exact Subtype.ext (hp'.trans hq'.symm)
  · intro cuts h
    cases cuts with
    | nil => exact (corner_contact_counterexample.2.2 h).elim
    | cons l cuts => simp

end Thesis.Polyomino
