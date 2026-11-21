import Thesis.PolyominoContacts

open Set

namespace Thesis.Polyomino

/-- Unit squares at a diagonal contact meet at the grid vertex whose
coordinates are the larger of their two lower-left coordinates. -/
def DiagonalContact (p q : Cell) : Prop :=
  (p.1+1 = q.1 ∨ q.1+1 = p.1) ∧ (p.2+1 = q.2 ∨ q.2+1 = p.2)

instance (p q : Cell) : Decidable (DiagonalContact p q) := by
  unfold DiagonalContact
  infer_instance

def contactVertex (p q : Cell) : Plane := fun a => (max (axisCoord p a) (axisCoord q a) : ℤ)

private theorem contact_coordinate {u v : ℤ} {z : ℝ}
    (hu : z ∈ Icc (u:ℝ) (u+1)) (hv : z ∈ Icc (v:ℝ) (v+1)) :
    u+1 = v ∨ v+1 = u ∨ u = v := by
  have huv : u ≤ v+1 := by exact_mod_cast hu.1.trans hv.2
  have hvu : v ≤ u+1 := by exact_mod_cast hv.1.trans hu.2
  omega

theorem diagonal_of_contact_without_side {p q : Cell} {z : Plane} (hne : p ≠ q)
    (hp : z ∈ cellSquare p) (hq : z ∈ cellSquare q) (hn : ∀ l, ¬SharedSide p q l) :
    DiagonalContact p q := by
  obtain ⟨px,py⟩ := p
  obtain ⟨qx,qy⟩ := q
  have hx := contact_coordinate (hp false) (hq false)
  have hy := contact_coordinate (hp true) (hq true)
  simp only [axisCoord, Bool.false_eq_true, ↓reduceIte] at hx hy
  rcases hx with hx|hx|hx <;> rcases hy with hy|hy|hy
  · exact ⟨Or.inl hx, Or.inl hy⟩
  · exact ⟨Or.inl hx, Or.inr hy⟩
  · exact (hn _ (Or.inl (Or.inl ⟨Prod.ext hx.symm hy.symm,rfl⟩))).elim
  · exact ⟨Or.inr hx,Or.inl hy⟩
  · exact ⟨Or.inr hx,Or.inr hy⟩
  · exact (hn _ (Or.inr (Or.inl ⟨Prod.ext hx.symm hy,rfl⟩))).elim
  · exact (hn _ (Or.inl (Or.inr ⟨Prod.ext hx.symm hy.symm,rfl⟩))).elim
  · exact (hn _ (Or.inr (Or.inr ⟨Prod.ext hx hy.symm,rfl⟩))).elim
  · exact (hne (Prod.ext hx hy)).elim

private theorem diagonal_axes {p q : Cell} (h : DiagonalContact p q) (a : Bool) :
    axisCoord p a+1 = axisCoord q a ∨ axisCoord q a+1 = axisCoord p a := by
  cases a
  · exact h.1
  · exact h.2

theorem diagonal_square_intersection {p q : Cell} (h : DiagonalContact p q) :
    cellSquare p ∩ cellSquare q = {contactVertex p q} := by
  ext z
  constructor
  · rintro ⟨hp,hq⟩
    apply Set.mem_singleton_iff.2
    funext a
    obtain ⟨pl,pu⟩ := hp a
    obtain ⟨ql,qu⟩ := hq a
    unfold contactVertex
    rcases diagonal_axes h a with f|f
    · rw [max_eq_right (by omega)]
      have e : (axisCoord p a:ℝ)+1 = axisCoord q a := by exact_mod_cast f
      exact le_antisymm (pu.trans e.le) ql
    · rw [max_eq_left (by omega)]
      have e : (axisCoord q a:ℝ)+1 = axisCoord p a := by exact_mod_cast f
      exact le_antisymm (qu.trans e.le) pl
  · rintro rfl
    constructor <;> intro a <;> unfold contactVertex <;>
      rcases diagonal_axes h a with f|f <;>
      first | (rw [max_eq_right (by omega)]; constructor <;> exact_mod_cast (by omega))
            | (rw [max_eq_left (by omega)]; constructor <;> exact_mod_cast (by omega))

/-- At a vertex there are exactly two complete grid lines which can remove
the point. This is the obstruction to the sufficiency step in §4.2. -/
theorem contactVertex_survives_iff {cells : List Cell} {cuts : List Line} {p q : CellIn cells}
    (h : DiagonalContact p.val q.val) :
    contactVertex p.val q.val ∈ remaining cells cuts ↔
      .vertical (max p.val.1 q.val.1) ∉ cuts ∧ .horizontal (max p.val.2 q.val.2) ∉ cuts := by
  constructor
  · intro hz
    exact ⟨fun hv => hz.2 false _ hv rfl, fun hh => hz.2 true _ hh rfl⟩
  · rintro ⟨hv,hh⟩
    have hpq : contactVertex p.val q.val ∈ cellSquare p.val ∩ cellSquare q.val := by
      rw [diagonal_square_intersection h]
      exact mem_singleton _
    refine ⟨⟨p,hpq.1⟩,?_⟩
    rintro axis c hc he
    unfold contactVertex at he
    have eq : max (axisCoord p.val axis) (axisCoord q.val axis) = c := by exact_mod_cast he
    subst c
    cases axis
    · exact hv hc
    · exact hh hc

/-- Finite, integer-only test of the author's family of grid-line cuts:
every shared side is cut and at least one line through each diagonal
contact vertex is cut. Quantification over real points disappears. -/
def CoversContacts (cells : List Cell) (cuts : List Line) : Prop :=
  Separates cells cuts ∧ ∀ p ∈ cells, ∀ q ∈ cells, DiagonalContact p q →
    Line.vertical (max p.1 q.1) ∈ cuts ∨ Line.horizontal (max p.2 q.2) ∈ cuts

instance (cells : List Cell) (cuts : List Line) : Decidable (CoversContacts cells cuts) := by
  unfold CoversContacts Separates
  infer_instance

theorem geometricallySeparated_iff_coversContacts (cells : List Cell) (cuts : List Line) :
    GeometricallySeparated cells cuts ↔ CoversContacts cells cuts := by
  constructor
  · intro h
    refine ⟨separates_of_geometricallySeparated h,?_⟩
    intro p hp q hq hd
    by_contra! hmiss
    let a : CellIn cells := ⟨p,hp⟩
    let b : CellIn cells := ⟨q,hq⟩
    have hz := (contactVertex_survives_iff (p:=a) (q:=b) hd).2 hmiss
    have hi : contactVertex p q ∈ cellSquare p ∩ cellSquare q := by
      rw [diagonal_square_intersection hd]
      exact mem_singleton _
    have eq := congrArg (fun c : CellIn cells => c.val.1)
      (geometricallySeparated_iff_unique_square.1 h a b _ hz hi.1 hi.2)
    change p.1 = q.1 at eq
    rcases hd.1 with h|h <;> omega
  · rintro ⟨side,corner⟩
    apply geometricallySeparated_iff_sides_and_contacts.2 ⟨side,?_⟩
    intro p q hn hside z hz hr
    have hd := diagonal_of_contact_without_side (fun eq => hn (Subtype.ext eq)) hz.1 hz.2 hside
    rw [diagonal_square_intersection hd,mem_singleton_iff] at hz
    subst z
    obtain ⟨hv,hh⟩ := (contactVertex_survives_iff hd).1 hr
    exact (corner p.val p.property q.val q.property hd).elim hv hh

theorem line_count_attained_iff_coversContacts (cells : List Cell) :
    (∃ cuts, GeometricallySeparated cells cuts ∧ cuts.length = (internalLines cells).length) ↔
      CoversContacts cells (internalLines cells) :=
  (line_count_attained_iff cells).trans (geometricallySeparated_iff_coversContacts _ _)

end Thesis.Polyomino
