import Thesis.Polyomino
import Mathlib.Logic.Relation

namespace Thesis.Polyomino

/-- The listed cells, with duplicates identified by their coordinates. -/
abbrev CellIn (cells : List Cell) := {p : Cell // p ∈ cells}

def PositiveSide (p q : Cell) (l : Line) : Prop :=
  (q = (p.1 + 1, p.2) ∧ l = .vertical (p.1 + 1)) ∨
  (q = (p.1, p.2 + 1) ∧ l = .horizontal (p.2 + 1))

def SharedSide (p q : Cell) (l : Line) : Prop :=
  PositiveSide p q l ∨ PositiveSide q p l

def RemainingAdjacent {cells : List Cell} (cuts : List Line) (p q : CellIn cells) : Prop :=
  ∃ l, SharedSide p.val q.val l ∧ l ∉ cuts

/-- Two cells lie in the same remaining part if a path of uncut shared
sides joins them. -/
def SamePart {cells : List Cell} (cuts : List Line) (p q : CellIn cells) : Prop :=
  Relation.ReflTransGen (RemainingAdjacent cuts) p q

def SeparatesIntoCells (cells : List Cell) (cuts : List Line) : Prop :=
  ∀ p q : CellIn cells, SamePart cuts p q → p = q

private theorem PositiveSide.ne {p q : Cell} {l : Line} (h : PositiveSide p q l) : p ≠ q := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · intro h
    have := congrArg Prod.fst h
    change _ = _ + 1 at this
    omega
  · intro h
    have := congrArg Prod.snd h
    change _ = _ + 1 at this
    omega

theorem cut_of_sharedSide {cells : List Cell} {cuts : List Line} (h : Separates cells cuts)
    {p q : CellIn cells} {l : Line} (hs : SharedSide p.val q.val l) : l ∈ cuts := by
  have cut_of_positive {a b : CellIn cells} {l : Line} (hs : PositiveSide a.val b.val l) :
      l ∈ cuts := by
    rcases hs with ⟨he, rfl⟩ | ⟨he, rfl⟩
    · exact (h a.val a.property).1 (he ▸ b.property)
    · exact (h a.val a.property).2 (he ▸ b.property)
  exact hs.elim cut_of_positive cut_of_positive

theorem separatesIntoCells_iff (cells : List Cell) (cuts : List Line) :
    SeparatesIntoCells cells cuts ↔ Separates cells cuts := by
  constructor
  · intro h p hp
    constructor
    · intro hq
      apply Decidable.byContradiction
      intro hcut
      let q : CellIn cells := ⟨(p.1 + 1, p.2), hq⟩
      have hside : PositiveSide p q.val (.vertical (p.1 + 1)) := Or.inl ⟨rfl, rfl⟩
      exact hside.ne (congrArg Subtype.val
        (h ⟨p, hp⟩ q (Relation.ReflTransGen.single ⟨_, Or.inl hside, hcut⟩)))
    · intro hq
      apply Decidable.byContradiction
      intro hcut
      let q : CellIn cells := ⟨(p.1, p.2 + 1), hq⟩
      have hside : PositiveSide p q.val (.horizontal (p.2 + 1)) := Or.inr ⟨rfl, rfl⟩
      exact hside.ne (congrArg Subtype.val
        (h ⟨p, hp⟩ q (Relation.ReflTransGen.single ⟨_, Or.inl hside, hcut⟩)))
  · intro h p q hpq
    induction hpq with
    | refl => rfl
    | tail _ hadj _ =>
      obtain ⟨_, hs, hnocut⟩ := hadj
      exact (hnocut (cut_of_sharedSide h hs)).elim

def SideConnected (cells : List Cell) : Prop :=
  ∀ p q : CellIn cells, SamePart [] p q

/-- The two coordinates, indexed by false (horizontal coordinate) and
true (vertical coordinate). -/
def axisCoord (p : Cell) (axis : Bool) : ℤ := if axis then p.2 else p.1

def axisLine (axis : Bool) (c : ℤ) : Line := if axis then .horizontal c else .vertical c

private theorem sharedSide_line_of_crossing {p q : Cell} {l : Line} (hs : SharedSide p q l)
    (axis : Bool) (c : ℤ) (hp : axisCoord p axis < c) (hq : c ≤ axisCoord q axis) :
    l = axisLine axis c := by
  rcases hs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    cases axis <;> simp [axisCoord, axisLine] at hp hq ⊢ <;> omega

/-- A path crossing an integer coordinate crosses a shared side on that line. -/
theorem sharedSide_exists_of_path_crossing {cells : List Cell}
    {p q : CellIn cells} (h : SamePart [] p q) (axis : Bool) (c : ℤ)
    (hp : axisCoord p.val axis < c) (hq : c ≤ axisCoord q.val axis) :
    ∃ u v : CellIn cells, SharedSide u.val v.val (axisLine axis c) := by
  induction h with
  | refl => omega
  | @tail q r _ hstep ih =>
    by_cases hl : axisCoord q.val axis < c
    · obtain ⟨l, hs, _⟩ := hstep
      exact ⟨q, r, (sharedSide_line_of_crossing hs axis c hl hq) ▸ hs⟩
    · exact ih (by omega)

/-- The minimum in thm:min-dissection-path with separation stated in
terms of the connected parts remaining after the full grid-line cuts. -/
theorem minimum_cuts_for_parts (cells : List Cell) :
    (∃ cuts, SeparatesIntoCells cells cuts ∧ cuts.length = (internalLines cells).length) ∧
    ∀ cuts, SeparatesIntoCells cells cuts → (internalLines cells).length ≤ cuts.length := by
  simpa only [separatesIntoCells_iff] using minimum_cuts cells

theorem rectangle_minimum_cuts_for_parts (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (∃ cuts, SeparatesIntoCells (rectangle a b) cuts ∧ cuts.length = (a - 1) + (b - 1)) ∧
    ∀ cuts, SeparatesIntoCells (rectangle a b) cuts → (a - 1) + (b - 1) ≤ cuts.length := by
  simpa only [rectangle_minimum_cuts a b ha hb] using minimum_cuts_for_parts (rectangle a b)

end Thesis.Polyomino
