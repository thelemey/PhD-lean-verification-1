import Thesis.PolyominoPieces
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

open Set

namespace Thesis.Polyomino

/-- The Euclidean plane in its two-coordinate product presentation. -/
abbrev Plane := Bool → ℝ

def cellSquare (p : Cell) : Set Plane :=
  {z | ∀ a, z a ∈ Icc (axisCoord p a : ℝ) ((axisCoord p a : ℝ) + 1)}

noncomputable def cellCenter (p : Cell) : Plane := fun a => (axisCoord p a : ℝ) + 1 / 2

/-- The original union of closed grid cells with the complete cut lines deleted. -/
def remaining (cells : List Cell) (cuts : List Line) : Set Plane :=
  {z | (∃ p : CellIn cells, z ∈ cellSquare p.val) ∧
    ∀ a c, axisLine a c ∈ cuts → z a ≠ (c : ℝ)}

def GeometricallySeparated (cells : List Cell) (cuts : List Line) : Prop :=
  ∀ p q : CellIn cells,
    cellCenter q.val ∈ connectedComponentIn (remaining cells cuts) (cellCenter p.val) → p = q

private theorem half_not_int (i j : ℤ) : (i : ℝ) + 1 / 2 ≠ (j : ℝ) := by
  intro h
  have hl : i < j := by exact_mod_cast (show (i : ℝ) < j by linarith)
  have hu : j < i + 1 := by exact_mod_cast (show (j : ℝ) < (i : ℝ) + 1 by linarith)
  omega

theorem cellCenter_mem_remaining {cells : List Cell} (cuts : List Line) (p : CellIn cells) :
    cellCenter p.val ∈ remaining cells cuts := by
  refine ⟨⟨p, fun axis => ⟨?_, ?_⟩⟩, fun axis c _ => half_not_int _ _⟩
  · dsimp [cellCenter]
    linarith
  · dsimp [cellCenter]
    linarith

/-- A point surviving in a unit square remains joined to its center.
The interior of the segment stays strictly between neighboring grid lines. -/
theorem mem_connectedComponent_of_cellSquare {cells : List Cell} {cuts : List Line}
    (p : CellIn cells) {z : Plane} (hz : z ∈ cellSquare p.val) (hr : z ∈ remaining cells cuts) :
    z ∈ connectedComponentIn (remaining cells cuts) (cellCenter p.val) := by
  let path : ℝ → Plane := fun t a => (1 - t) * cellCenter p.val a + t * z a
  let I := Icc (0 : ℝ) 1
  have hpath : Continuous path := by
    apply continuous_pi
    intro a
    dsimp only [path]
    fun_prop
  have hp : path 0 = cellCenter p.val := by funext a; simp [path]
  have hq : path 1 = z := by funext a; simp [path]
  have hsub : path '' I ⊆ remaining cells cuts := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    by_cases he : t = 1
    · rw [he, hq]
      exact hr
    have hc : 0 < 1 - t := sub_pos.2 (lt_of_le_of_ne ht1 he)
    have within (a : Bool) : (axisCoord p.val a : ℝ) < path t a ∧
        path t a < (axisCoord p.val a : ℝ) + 1 := by
      obtain ⟨hl, hu⟩ := hz a
      have hzl := mul_le_mul_of_nonneg_left hl ht0
      have hzu := mul_le_mul_of_nonneg_left hu ht0
      have hcl : (axisCoord p.val a : ℝ) < cellCenter p.val a := by
        unfold cellCenter
        linarith
      have hcu : cellCenter p.val a < (axisCoord p.val a : ℝ) + 1 := by
        unfold cellCenter
        linarith
      have hcl' := mul_lt_mul_of_pos_left hcl hc
      have hcu' := mul_lt_mul_of_pos_left hcu hc
      unfold path
      exact ⟨by linarith only [hzl, hcl'], by linarith only [hzu, hcu']⟩
    refine ⟨⟨p, fun a => ⟨(within a).1.le, (within a).2.le⟩⟩, ?_⟩
    intro a c _ h
    have hlo : axisCoord p.val a < c := by
      exact_mod_cast (show (axisCoord p.val a : ℝ) < c from h ▸ (within a).1)
    have hhi : c < axisCoord p.val a + 1 := by
      exact_mod_cast (show (c : ℝ) < (axisCoord p.val a : ℝ) + 1 from h ▸ (within a).2)
    omega
  have hstart : cellCenter p.val ∈ path '' I := ⟨0, by norm_num [I], hp⟩
  have hfinish : z ∈ path '' I := ⟨1, by norm_num [I], hq⟩
  exact (isPreconnected_Icc.image path hpath.continuousOn).subset_connectedComponentIn hstart hsub hfinish

/-- The center criterion says exactly that the remaining parts are the
surviving portions of the individual original squares. Every remaining
point belongs to the part of the center of one of its squares. -/
theorem geomSeparated_iff_components {cells : List Cell} {cuts : List Line} :
    GeometricallySeparated cells cuts ↔ ∀ p : CellIn cells,
      connectedComponentIn (remaining cells cuts) (cellCenter p.val) =
        cellSquare p.val ∩ remaining cells cuts := by
  constructor
  · intro h p
    ext z
    constructor
    · intro hz
      have hr := connectedComponentIn_subset _ _ hz
      obtain ⟨q, hq⟩ := hr.1
      have hzq := mem_connectedComponent_of_cellSquare q hq hr
      have eq_components := (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hzq).symm
      have hqc : cellCenter q.val ∈ connectedComponentIn (remaining cells cuts) (cellCenter p.val) := by
        rw [eq_components]
        exact mem_connectedComponentIn (cellCenter_mem_remaining cuts q)
      have he := h p q hqc
      exact ⟨he ▸ hq, hr⟩
    · exact fun hz => mem_connectedComponent_of_cellSquare p hz.1 hz.2
  · intro h p q hpq
    have hhalf := ((h p) ▸ hpq).1
    have eq_coord (a : Bool) : axisCoord p.val a = axisCoord q.val a := by
      have hlow : (axisCoord p.val a : ℝ) ≤ (axisCoord q.val a : ℝ) + 1 / 2 := (hhalf a).1
      have hhigh : (axisCoord q.val a : ℝ) + 1 / 2 ≤ (axisCoord p.val a : ℝ) + 1 := (hhalf a).2
      have hl : axisCoord p.val a < axisCoord q.val a + 1 := by
        exact_mod_cast (show (axisCoord p.val a : ℝ) < (axisCoord q.val a : ℝ) + 1 by linarith)
      have hh : axisCoord q.val a < axisCoord p.val a + 1 := by
        exact_mod_cast (show (axisCoord q.val a : ℝ) < (axisCoord p.val a : ℝ) + 1 by linarith)
      omega
    exact Subtype.ext (Prod.ext (eq_coord false) (eq_coord true))

theorem positiveSide_axis {p q : Cell} {l : Line} (h : PositiveSide p q l) :
    ∃ a : Bool, l = axisLine a (axisCoord p a + 1) ∧
      ∀ d : Bool, axisCoord q d = axisCoord p d + if d = a then 1 else 0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨false, rfl, fun d => by cases d <;> simp [axisCoord]⟩
  · exact ⟨true, rfl, fun d => by cases d <;> simp [axisCoord]⟩

/-- If the common side is left uncut, the straight segment joining the
two cell centers stays in the same geometric part. -/
theorem same_geometricPart_of_uncut_positiveSide {cells : List Cell} {cuts : List Line}
    {p q : CellIn cells} {l : Line} (hs : PositiveSide p.val q.val l) (hc : l ∉ cuts) :
    cellCenter q.val ∈ connectedComponentIn (remaining cells cuts) (cellCenter p.val) := by
  obtain ⟨a, rfl, hcoord⟩ := positiveSide_axis hs
  let path : ℝ → Plane := fun t d => cellCenter p.val d + if d = a then t else 0
  let I := Icc (0 : ℝ) 1
  have hpath : Continuous path := by
    apply continuous_pi
    intro d
    by_cases hd : d = a
    · simpa only [path, hd, if_true] using
        (continuous_const.add continuous_id :
          Continuous fun t : ℝ => cellCenter p.val d + t)
    · simp only [path, hd, if_false, add_zero]
      exact continuous_const
  have hp : path 0 = cellCenter p.val := by
    funext d
    simp [path]
  have hq : path 1 = cellCenter q.val := by
    funext d
    by_cases hd : d = a
    · simp [path, cellCenter, hcoord, hd]
      ring
    · simp [path, cellCenter, hcoord, hd]
  have hsub : path '' I ⊆ remaining cells cuts := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    constructor
    · by_cases ht : t ≤ 1 / 2
      · refine ⟨p, fun d => ?_⟩
        change _ ≤ path t d ∧ path t d ≤ _
        by_cases hd : d = a <;> simp only [path, cellCenter, hd, if_true, if_false, add_zero] <;> constructor <;> linarith
      · refine ⟨q, fun d => ?_⟩
        change _ ≤ path t d ∧ path t d ≤ _
        by_cases hd : d = a <;> simp only [path, cellCenter, hcoord, hd, if_true, if_false, add_zero,
          Int.cast_add, Int.cast_one] <;> constructor <;> linarith
    · intro d c hcut hpoint
      by_cases hd : d = a
      · subst d
        simp only [path, cellCenter, if_true] at hpoint
        have hlo : axisCoord p.val a < c := by
          exact_mod_cast (show (axisCoord p.val a : ℝ) < c by linarith)
        have hhi : c < axisCoord p.val a + 2 := by
          exact_mod_cast (show (c : ℝ) < (axisCoord p.val a : ℝ) + 2 by linarith)
        have he : c = axisCoord p.val a + 1 := by omega
        exact hc (he ▸ hcut)
      · exact half_not_int _ _ (by simpa only [path, cellCenter, hd, if_false, add_zero] using hpoint)
  have hstart : cellCenter p.val ∈ path '' I := ⟨0, by norm_num [I], hp⟩
  have hfinish : cellCenter q.val ∈ path '' I := ⟨1, by norm_num [I], hq⟩
  exact (isPreconnected_Icc.image path hpath.continuousOn).subset_connectedComponentIn hstart hsub hfinish

private theorem centers_straddling_cut {cells : List Cell} {cuts : List Line} {p q : CellIn cells}
    {C : Set Plane} (hC : IsPreconnected C) (hsub : C ⊆ remaining cells cuts)
    (hp : cellCenter p.val ∈ C) (hq : cellCenter q.val ∈ C)
    {a : Bool} {c : ℤ} (hcut : axisLine a c ∈ cuts)
    (hlo : axisCoord p.val a < c) (hhi : c ≤ axisCoord q.val a) : False := by
  have hl : (axisCoord p.val a : ℝ) + 1 ≤ c := by
    exact_mod_cast (show axisCoord p.val a + 1 ≤ c by omega)
  have hh : (c : ℝ) ≤ axisCoord q.val a := by exact_mod_cast hhi
  have hc : (c : ℝ) ∈ Icc (cellCenter p.val a) (cellCenter q.val a) := by
    simp only [cellCenter, mem_Icc]
    constructor <;> linarith
  have hcont : Continuous (fun z : Plane => z a) := continuous_apply a
  obtain ⟨z, hz, he⟩ := hC.intermediate_value hp hq hcont.continuousOn hc
  exact (hsub hz).2 a c hcut he

/-- Two cells sharing a side remain in the same geometric component
exactly when the line of that side is left uncut. -/
theorem same_geometricPart_iff_uncut_side {cells : List Cell} {cuts : List Line}
    {p q : CellIn cells} {l : Line} (hside : SharedSide p.val q.val l) :
    cellCenter q.val ∈ connectedComponentIn (remaining cells cuts) (cellCenter p.val) ↔
      l ∉ cuts := by
  have forward {u v : CellIn cells} (h : PositiveSide u.val v.val l)
      (hv : cellCenter v.val ∈ connectedComponentIn (remaining cells cuts) (cellCenter u.val)) :
      l ∉ cuts := by
    intro hcut
    obtain ⟨a, rfl, hcoord⟩ := positiveSide_axis h
    have hl : axisCoord u.val a < axisCoord u.val a + 1 := by omega
    have hh : axisCoord u.val a + 1 ≤ axisCoord v.val a := by
      simp only [hcoord, if_true, le_refl]
    exact centers_straddling_cut isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _)
      (mem_connectedComponentIn (cellCenter_mem_remaining cuts u)) hv hcut hl hh
  have reverse {u v : CellIn cells}
      (hv : cellCenter v.val ∈ connectedComponentIn (remaining cells cuts) (cellCenter u.val)) :
      cellCenter u.val ∈ connectedComponentIn (remaining cells cuts) (cellCenter v.val) := by
    rw [← connectedComponentIn_eq hv]
    exact mem_connectedComponentIn (cellCenter_mem_remaining cuts u)
  rcases hside with h | h
  · exact ⟨forward h, same_geometricPart_of_uncut_positiveSide h⟩
  · exact ⟨fun hv => forward h (reverse hv),
      fun hcut => reverse (same_geometricPart_of_uncut_positiveSide h hcut)⟩

/-- Every separating family must cut each internal side, even if some
components of the original union meet only at a vertex. -/
theorem separates_of_geometricallySeparated {cells : List Cell} {cuts : List Line}
    (h : GeometricallySeparated cells cuts) : Separates cells cuts := by
  intro p hp
  constructor
  · intro hq
    by_contra hc
    let q : CellIn cells := ⟨(p.1 + 1, p.2), hq⟩
    have hside : SharedSide p q.val (.vertical (p.1 + 1)) := Or.inl (Or.inl ⟨rfl, rfl⟩)
    have hsame := (same_geometricPart_iff_uncut_side
      (p := ⟨p, hp⟩) (q := q) hside).2 hc
    have he := congrArg (fun x : CellIn cells => x.val.1) (h _ _ hsame)
    change p.1 = p.1 + 1 at he
    omega
  · intro hq
    by_contra hc
    let q : CellIn cells := ⟨(p.1, p.2 + 1), hq⟩
    have hside : SharedSide p q.val (.horizontal (p.2 + 1)) := Or.inl (Or.inr ⟨rfl, rfl⟩)
    have hsame := (same_geometricPart_iff_uncut_side
      (p := ⟨p, hp⟩) (q := q) hside).2 hc
    have he := congrArg (fun x : CellIn cells => x.val.2) (h _ _ hsame)
    change p.2 = p.2 + 1 at he
    omega

/-- The sufficiency step in the line-count proof. Each grid line between
two centers must support a shared edge somewhere in the polyomino. -/
theorem geometricallySeparated_iff_of_crossings {cells : List Cell}
    (crossing : ∀ (u v : CellIn cells) (a : Bool) (c : ℤ),
      axisCoord u.val a < c → c ≤ axisCoord v.val a →
      ∃ x y : CellIn cells, SharedSide x.val y.val (axisLine a c))
    (cuts : List Line) : GeometricallySeparated cells cuts ↔ Separates cells cuts := by
  constructor
  · exact separates_of_geometricallySeparated
  · intro h p q hq
    let C := connectedComponentIn (remaining cells cuts) (cellCenter p.val)
    have hC : IsPreconnected C := isPreconnected_connectedComponentIn
    have hsub : C ⊆ remaining cells cuts := connectedComponentIn_subset _ _
    have hp : cellCenter p.val ∈ C := mem_connectedComponentIn (cellCenter_mem_remaining cuts p)
    have no_ascending {u v : CellIn cells} (hu : cellCenter u.val ∈ C)
        (hv : cellCenter v.val ∈ C) (a : Bool) (hlt : axisCoord u.val a < axisCoord v.val a) :
        False := by
      let c := axisCoord u.val a + 1
      have hlo : axisCoord u.val a < c := by dsimp [c]; omega
      have hhi : c ≤ axisCoord v.val a := by dsimp [c]; omega
      obtain ⟨x, y, hside⟩ := crossing u v a c hlo hhi
      exact centers_straddling_cut hC hsub hu hv (cut_of_sharedSide h hside) hlo hhi
    have eq_coord (a : Bool) : axisCoord p.val a = axisCoord q.val a := by
      apply le_antisymm
      · exact le_of_not_gt (no_ascending hq hp a)
      · exact le_of_not_gt (no_ascending hp hq a)
    apply Subtype.ext
    exact Prod.ext (eq_coord false) (eq_coord true)

/-- A side-connected polyomino satisfies the required crossing condition. -/
theorem geometricallySeparated_iff {cells : List Cell} (hconn : SideConnected cells)
    (cuts : List Line) : GeometricallySeparated cells cuts ↔ Separates cells cuts :=
  geometricallySeparated_iff_of_crossings
    (fun p q => sharedSide_exists_of_path_crossing (hconn p q)) cuts

theorem minimum_geometric_cuts {cells : List Cell} (hconn : SideConnected cells) :
    (∃ cuts, GeometricallySeparated cells cuts ∧ cuts.length = (internalLines cells).length) ∧
    ∀ cuts, GeometricallySeparated cells cuts → (internalLines cells).length ≤ cuts.length := by
  simpa only [geometricallySeparated_iff hconn] using minimum_cuts cells

/-- The rectangle case with components of the geometric remainder as the pieces. -/
theorem rectangle_minimum_geometric_cuts (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (∃ cuts, GeometricallySeparated (rectangle a b) cuts ∧ cuts.length = (a - 1) + (b - 1)) ∧
    ∀ cuts, GeometricallySeparated (rectangle a b) cuts → (a - 1) + (b - 1) ≤ cuts.length := by
  simpa only [rectangle_minimum_cuts a b ha hb] using
    minimum_geometric_cuts (sideConnected_rectangle a b ha hb)

private def cornerPair : List Cell := [(0, 0), (1, 1)]

/-- If "connected union" allows contact at a corner only, the source's
line-count criterion fails. There are no shared sides but the two squares
belong to a single connected component before any cuts. -/
theorem corner_contact_counterexample :
    IsConnected (remaining cornerPair []) ∧ internalLines cornerPair = [] ∧
      ¬ GeometricallySeparated cornerPair [] := by
  let p : CellIn cornerPair := ⟨(0, 0), by decide⟩
  let q : CellIn cornerPair := ⟨(1, 1), by decide⟩
  let z : Plane := fun _ => 1
  let F := remaining cornerPair []
  have hzP : z ∈ cellSquare p.val := by
    intro a
    cases a <;> norm_num [z, p, axisCoord]
  have hzQ : z ∈ cellSquare q.val := by
    intro a
    cases a <;> norm_num [z, q, axisCoord]
  have hzF : z ∈ F := ⟨⟨p, hzP⟩, by simp⟩
  have hzP' := mem_connectedComponent_of_cellSquare p hzP hzF
  have hzQ' := mem_connectedComponent_of_cellSquare q hzQ hzF
  have he : connectedComponentIn F (cellCenter p.val) = connectedComponentIn F (cellCenter q.val) :=
    (connectedComponentIn_eq hzP').trans (connectedComponentIn_eq hzQ').symm
  have hp := cellCenter_mem_remaining [] p
  have hq := cellCenter_mem_remaining [] q
  have heq : connectedComponentIn F (cellCenter p.val) = F := by
    apply (connectedComponentIn_subset _ _).antisymm
    intro x hx
    obtain ⟨r, hr⟩ := hx.1
    have hmem := mem_connectedComponent_of_cellSquare r hr hx
    have hcases : r.val = (0, 0) ∨ r.val = (1, 1) := by
      simpa only [cornerPair, List.mem_cons, List.not_mem_nil, or_false] using r.property
    rcases hcases with h | h
    · have h' : r = p := Subtype.ext h
      exact h' ▸ hmem
    · have h' : r = q := Subtype.ext h
      exact he ▸ (h' ▸ hmem)
  have hF : IsConnected F := by
    rw [← heq]
    exact isConnected_connectedComponentIn_iff.2 hp
  refine ⟨hF, by decide, ?_⟩
  intro h
  have hsame : cellCenter q.val ∈ connectedComponentIn F (cellCenter p.val) :=
    he ▸ mem_connectedComponentIn hq
  have hcoord := congrArg (fun r : CellIn cornerPair => r.val.1) (h p q hsame)
  change (0 : ℤ) = 1 at hcoord
  omega

end Thesis.Polyomino
