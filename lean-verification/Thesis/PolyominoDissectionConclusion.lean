import Thesis.PolyominoGridContacts

namespace Thesis.Polyomino

/-- A finite family of full grid lines suffices for any finite union of cells.
The internal lines remove every shared side. The vertical lines through
the listed left edges also remove every diagonal contact vertex. -/
private theorem cut_length_exists (cells : List Cell) :
    ∃ n : ℕ, ∃ cuts : List Line, GeometricallySeparated cells cuts ∧ cuts.length = n := by
  let verticals := cells.map (fun p => Line.vertical p.1)
  let cuts := internalLines cells ++ verticals
  refine ⟨cuts.length, cuts, (geometricallySeparated_iff_coversContacts _ _).2 ⟨?_, ?_⟩, rfl⟩
  · exact (separates_iff _ _).2 fun _ hl => List.mem_append_left _ hl
  · intro p hp q hq _
    apply Or.inl
    apply List.mem_append_right
    rcases le_total p.1 q.1 with h | h
    · rw [max_eq_right h]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
    · rw [max_eq_left h]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩

/-- Minimum number of full grid lines when the pieces have the geometric
connected-component meaning used in the proof of Theorem 4.2.1. -/
noncomputable def geometricCutCount (cells : List Cell) : ℕ := by
  classical exact Nat.find (cut_length_exists cells)

theorem geometricCutCount_spec (cells : List Cell) :
    (∃ cuts, GeometricallySeparated cells cuts ∧ cuts.length = geometricCutCount cells) ∧
    ∀ cuts, GeometricallySeparated cells cuts → geometricCutCount cells ≤ cuts.length := by
  classical
  exact ⟨Nat.find_spec (cut_length_exists cells),
    fun cuts hs => Nat.find_min' (cut_length_exists cells) ⟨cuts, hs, rfl⟩⟩

/-- The lower bound in the source always holds. Its proposed cuts attain
it exactly when they also remove the diagonal contacts. -/
theorem geometricCutCount_eq_internal_iff (cells : List Cell) :
    geometricCutCount cells = (internalLines cells).length ↔ CoversContacts cells (internalLines cells) := by
  obtain ⟨⟨best, separated, length⟩, lower⟩ := geometricCutCount_spec cells
  have mandatory := (minimum_cuts cells).2 best (separates_of_geometricallySeparated separated)
  rw [length] at mandatory
  constructor
  · intro eq
    exact (line_count_attained_iff_coversContacts cells).1 ⟨best, separated, length.trans eq⟩
  · intro covered
    exact le_antisymm (lower _ ((geometricallySeparated_iff_coversContacts _ _).2 covered)) mandatory

/-- The source argument with the usual side-connectivity hypothesis for
polyominoes, and its stated rectangular specialization. -/
theorem dissection_formula_of_sideConnected (cells : List Cell) (h : SideConnected cells) :
    geometricCutCount cells = (internalLines cells).length := by
  exact (geometricCutCount_eq_internal_iff cells).2
    ((line_count_attained_iff_coversContacts cells).1 (minimum_geometric_cuts h).1)

theorem rectangle_geometricCutCount (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    geometricCutCount (rectangle a b) = (a-1)+(b-1) :=
  (dissection_formula_of_sideConnected _ (sideConnected_rectangle a b ha hb)).trans
    (rectangle_minimum_cuts a b ha hb)

/-- A connected union of two distinct cells satisfies the literal definition
in §4.2, has no internal lines, and has geometric minimum exactly one. -/
theorem corner_pair_dissection :
    let cells : List Cell := [(0,0), (1,1)]
    IsConnected (remaining cells []) ∧ (internalLines cells).length = 0 ∧ geometricCutCount cells = 1 := by
  intro cells
  obtain ⟨noLines, oneCut, atLeastOne⟩ := corner_contact_minimum_one
  obtain ⟨⟨best, separated, length⟩, lower⟩ := geometricCutCount_spec cells
  exact ⟨corner_contact_counterexample.1, congrArg List.length noLines,
    le_antisymm (lower [.vertical 1] oneCut) (length ▸ atLeastOne best separated)⟩

/-- Negation of the universally quantified equality under the connected-union
definition printed in §4.2, even for lists with no repeated cells. -/
theorem dissection_formula_as_printed_false :
    ¬ ∀ cells : List Cell, cells.Nodup → IsConnected (remaining cells []) →
      geometricCutCount cells = (internalLines cells).length := by
  intro claim
  obtain ⟨connected, zeroLines, oneCut⟩ := corner_pair_dissection
  have eq := claim [(0,0), (1,1)] (by decide) connected
  omega

end Thesis.Polyomino
