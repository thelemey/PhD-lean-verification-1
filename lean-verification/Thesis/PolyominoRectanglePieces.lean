import Thesis.PolyominoContactPaths
import Mathlib.Analysis.Convex.Topology

open Set

namespace Thesis.Polyomino

/-- In the rectangular case of §4.2 an intermediate piece is determined
by the side of each already removed line. This applies to any order of
cuts, including repeated lines and cuts outside the board. -/
theorem rectangle_piece_iff_same_side {a b : ℕ} (cuts : List Line) (p q : CellIn (rectangle a b)) :
    cellCenter q.val ∈ connectedComponentIn (remaining (rectangle a b) cuts) (cellCenter p.val) ↔
      ∀ d c, axisLine d c ∈ cuts → (axisCoord p.val d < c ↔ axisCoord q.val d < c) := by
  have hp := mem_connectedComponentIn (cellCenter_mem_remaining cuts p)
  constructor
  · intro h d c hc
    constructor
    · intro hl
      by_contra! hi
      exact centers_straddling_cut isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) hp h hc hl hi
    · intro hl
      by_contra! hi
      exact centers_straddling_cut isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) h hp hc hl hi
  · intro same
    let C := univ.pi fun d => Icc (min (cellCenter p.val d) (cellCenter q.val d))
      (max (cellCenter p.val d) (cellCenter q.val d))
    have pre : IsPreconnected C := (convex_pi (𝕜:=ℝ) (fun _ _ => convex_Icc _ _)).isPreconnected
    have pc : cellCenter p.val ∈ C := fun _ _ => ⟨min_le_left _ _,le_max_left _ _⟩
    have qc : cellCenter q.val ∈ C := fun _ _ => ⟨min_le_right _ _,le_max_right _ _⟩
    apply pre.subset_connectedComponentIn pc _ qc
    intro z hz
    have inside (r : CellIn (rectangle a b)) (d : Bool) :
        0 ≤ cellCenter r.val d ∧ cellCenter r.val d < (if d then (b:ℝ) else (a:ℝ)) := by
      obtain ⟨x0,x1,y0,y1⟩ := mem_rectangle.1 r.property
      have X : (r.val.1:ℝ)+1 ≤ a := by exact_mod_cast (Int.add_one_le_of_lt x1)
      have Y : (r.val.2:ℝ)+1 ≤ b := by exact_mod_cast (Int.add_one_le_of_lt y1)
      have X0 : 0 ≤ (r.val.1:ℝ) := by exact_mod_cast x0
      have Y0 : 0 ≤ (r.val.2:ℝ) := by exact_mod_cast y0
      cases d <;> simp only [cellCenter,axisCoord,Bool.false_eq_true,↓reduceIte] <;> constructor <;> linarith
    have bounds (d) : 0 ≤ z d ∧ z d < (if d then (b:ℝ) else (a:ℝ)) :=
      ⟨(le_min (inside p d).1 (inside q d).1).trans (hz d trivial).1,
       (hz d trivial).2.trans_lt (max_lt (inside p d).2 (inside q d).2)⟩
    have xf : ⌊z false⌋ < (a:ℤ) := Int.floor_lt.2 (by simpa using (bounds false).2)
    have yf : ⌊z true⌋ < (b:ℤ) := Int.floor_lt.2 (by simpa using (bounds true).2)
    let r : CellIn (rectangle a b) := ⟨(⌊z false⌋,⌊z true⌋),mem_rectangle.2
      ⟨Int.floor_nonneg.2 (bounds false).1,xf,Int.floor_nonneg.2 (bounds true).1,yf⟩⟩
    refine ⟨⟨r,fun d => ?_⟩,?_⟩
    · cases d <;> exact ⟨Int.floor_le _,(Int.lt_floor_add_one _).le⟩
    · intro d c hc
      have below (s : Cell) (h : axisCoord s d < c) : cellCenter s d < c := by
        have he : (axisCoord s d:ℝ)+1 ≤ c := by exact_mod_cast (show axisCoord s d+1 ≤ c by omega)
        dsimp only [cellCenter]; linarith
      have above (s : Cell) (h : ¬axisCoord s d < c) : (c:ℝ) < cellCenter s d := by
        have he : (c:ℝ) ≤ axisCoord s d := by exact_mod_cast (le_of_not_gt h)
        dsimp only [cellCenter]; linarith
      by_cases side : axisCoord p.val d < c
      · exact ((hz d trivial).2.trans_lt (max_lt (below _ side) (below _ ((same d c hc).1 side)))).ne
      · exact ((lt_min (above _ side) (above _ (fun h => side ((same d c hc).2 h)))).trans_le (hz d trivial).1).ne'

/-- The two square boards in the example immediately after the unit-edge
remark: the explicit cut lines attain the minimum and both counts are
strictly below N−1. -/
theorem square_examples_cut_counts :
    let two := [Line.vertical 1,.horizontal 1]
    let three := [Line.vertical 1,.vertical 2,.horizontal 1,.horizontal 2]
    GeometricallySeparated (rectangle 2 2) two ∧ two.length = 2 ∧
      two.length < (rectangle 2 2).length-1 ∧
      (∀ c, GeometricallySeparated (rectangle 2 2) c → two.length ≤ c.length) ∧
    GeometricallySeparated (rectangle 3 3) three ∧ three.length = 4 ∧
      three.length < (rectangle 3 3).length-1 ∧
      ∀ c, GeometricallySeparated (rectangle 3 3) c → three.length ≤ c.length := by
  intro two three
  exact ⟨(geometricallySeparated_iff_coversContacts _ _).2 (by decide),rfl,by decide,
    (rectangle_minimum_geometric_cuts 2 2 (by decide) (by decide)).2,
    (geometricallySeparated_iff_coversContacts _ _).2 (by decide),rfl,by decide,
    (rectangle_minimum_geometric_cuts 3 3 (by decide) (by decide)).2⟩

end Thesis.Polyomino
