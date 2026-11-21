import Thesis.PolyominoUnitEdges

open Set

namespace Thesis.Polyomino

/-- Pieces are kept in place. Applying the second list of full grid lines
to all current pieces deletes the same points as the concatenated cut list. -/
theorem remaining_append (cells : List Cell) (first second : List Line) :
    remaining cells (first++second) =
      remaining cells first ∩ {z | ∀ a c, axisLine a c ∈ second → z a ≠ (c:ℝ)} := by
  ext z
  simp only [remaining, List.mem_append, Set.mem_setOf_eq,Set.mem_inter_iff]
  constructor
  · rintro ⟨hp,h⟩
    exact ⟨⟨hp,fun a c h₁ => h a c (Or.inl h₁)⟩,fun a c h₂ => h a c (Or.inr h₂)⟩
  · rintro ⟨⟨hp,h₁⟩,h₂⟩
    exact ⟨hp,fun a c h => h.elim (h₁ a c) (h₂ a c)⟩

private theorem certified_minimum {cells : List Cell} {cuts : List Line} {n : ℕ}
    (check : CoversContacts cells cuts) (hc : cuts.length = n) (hl : (internalLines cells).length = n) :
    GeometricallySeparated cells cuts ∧ cuts.length = n ∧
      ∀ other, GeometricallySeparated cells other → n ≤ other.length :=
  ⟨(geometricallySeparated_iff_coversContacts _ _).2 check,hc,fun other h => hl ▸
    (minimum_cuts cells).2 other (separates_of_geometricallySeparated h)⟩

theorem domino_one_cut :
    let cells : List Cell := [(0,0),(1,0)]
    GeometricallySeparated cells [.vertical 1] ∧ ([Line.vertical 1].length = 1) ∧
      ∀ cuts, GeometricallySeparated cells cuts → 1 ≤ cuts.length :=
  certified_minimum (by decide) rfl (by decide)

theorem l_tromino_two_cuts :
    let cells : List Cell := [(0,0),(1,0),(0,1)]
    let cuts := [Line.vertical 1,Line.horizontal 1]
    GeometricallySeparated cells cuts ∧ cuts.length = 2 ∧
      ∀ other, GeometricallySeparated cells other → 2 ≤ other.length :=
  certified_minimum (by decide) rfl (by decide)

/-- After the first cut in the L-tromino example the upper cell stays with
the lower-left cell; the right-hand cell has already been detached. -/
theorem l_tromino_first_cut :
    let cells : List Cell := [(0,0),(1,0),(0,1)]
    let origin : CellIn cells := ⟨(0,0),by decide⟩
    let right : CellIn cells := ⟨(1,0),by decide⟩
    let top : CellIn cells := ⟨(0,1),by decide⟩
    let component := connectedComponentIn (remaining cells [.vertical 1]) (cellCenter origin.val)
    cellCenter top.val ∈ component ∧ cellCenter right.val ∉ component := by
  intro cells origin right top component
  have h₁ : PositiveSide origin.val top.val (.horizontal 1) := Or.inr ⟨rfl,rfl⟩
  have h₂ : PositiveSide origin.val right.val (.vertical 1) := Or.inl ⟨rfl,rfl⟩
  exact ⟨same_geometricPart_of_uncut_positiveSide h₁ (by decide),
    fun h => ((same_geometricPart_iff_uncut_side (cuts := [.vertical 1]) (p := origin) (q := right)
      (Or.inl h₂)).1 h) (by decide)⟩

end Thesis.Polyomino
