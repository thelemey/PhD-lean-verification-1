import Thesis.FiniteList

namespace Thesis.Polyomino

abbrev Cell := Int × Int

inductive Line
  | vertical : Int → Line
  | horizontal : Int → Line
  deriving DecidableEq

/-- A cell is represented by its bottom-left corner. Each shared unit side
is enumerated once by looking to the right and upwards from each cell in
the input (possibly with repetitions if the input repeats a cell). -/
def sideLines (cells : List Cell) : List Line :=
  (cells.filterMap fun p => if (p.1 + 1, p.2) ∈ cells then
    some (.vertical (p.1 + 1)) else none) ++
  (cells.filterMap fun p => if (p.1, p.2 + 1) ∈ cells then
    some (.horizontal (p.2 + 1)) else none)

private def uniqueLines : List Line → List Line
  | [] => []
  | l :: ls => if l ∈ ls then uniqueLines ls else l :: uniqueLines ls

private theorem mem_uniqueLines (l : Line) (ls : List Line) :
    l ∈ uniqueLines ls ↔ l ∈ ls := by
  induction ls with
  | nil => simp [uniqueLines]
  | cons a ls ih =>
    by_cases ha : a ∈ ls
    · rw [uniqueLines, if_pos ha, ih]
      exact ⟨List.mem_cons_of_mem _, fun h => (List.mem_cons.mp h).elim
        (fun e => e ▸ ha) id⟩
    · simp [uniqueLines, ha, ih]

private theorem uniqueLines_nodup (ls : List Line) : (uniqueLines ls).Nodup := by
  induction ls with
  | nil => simp [uniqueLines]
  | cons a ls ih =>
    by_cases ha : a ∈ ls
    · simpa [uniqueLines, ha] using ih
    · simpa [uniqueLines, ha, List.nodup_cons, mem_uniqueLines] using ih

def internalLines (cells : List Cell) : List Line := uniqueLines (sideLines cells)

/-- The remaining cell-adjacency graph has singleton components precisely
when every shared side is cut. Each side lies on a unique grid line. -/
def Separates (cells : List Cell) (cuts : List Line) : Prop :=
  ∀ p ∈ cells,
    ((p.1 + 1, p.2) ∈ cells → Line.vertical (p.1 + 1) ∈ cuts) ∧
    ((p.1, p.2 + 1) ∈ cells → Line.horizontal (p.2 + 1) ∈ cuts)

theorem separates_iff (cells : List Cell) (cuts : List Line) :
    Separates cells cuts ↔ ∀ l ∈ internalLines cells, l ∈ cuts := by
  simp only [internalLines, mem_uniqueLines, sideLines, List.mem_append, List.mem_filterMap]
  constructor
  · intro h l hl
    rcases hl with ⟨p, hp, he⟩ | ⟨p, hp, he⟩
    · split at he
      · rename_i hq
        cases Option.some.inj he
        exact (h p hp).1 hq
      · contradiction
    · split at he
      · rename_i hq
        cases Option.some.inj he
        exact (h p hp).2 hq
      · contradiction
  · intro h p hp
    exact ⟨fun hq => h _ (.inl ⟨p, hp, by simp [hq]⟩),
      fun hq => h _ (.inr ⟨p, hp, by simp [hq]⟩)⟩

/-- The general minimum in `thm:min-dissection-path`. This result also
holds for disconnected cell sets and lists of cuts with repetitions. -/
theorem minimum_cuts (cells : List Cell) :
    (∃ cuts, Separates cells cuts ∧ cuts.length = (internalLines cells).length) ∧
    ∀ cuts, Separates cells cuts → (internalLines cells).length ≤ cuts.length := by
  refine ⟨⟨internalLines cells, (separates_iff _ _).2 (fun _ h => h), rfl⟩, ?_⟩
  intro cuts h
  exact FiniteList.nodup_length_le_of_subset (uniqueLines_nodup _) ((separates_iff _ _).1 h)

/-- The `a × b` rectangle based at the origin. -/
def rectangle (a b : Nat) : List Cell :=
  (List.range a).flatMap fun (x : Nat) => (List.range b).map fun (y : Nat) => ((x : Int), (y : Int))

theorem mem_rectangle {a b : Nat} {x y : Int} :
    (x, y) ∈ rectangle a b ↔ 0 ≤ x ∧ x < a ∧ 0 ≤ y ∧ y < b := by
  simp only [rectangle, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, j, hj, rfl, rfl⟩
    omega
  · rintro ⟨hx, hxa, hy, hyb⟩
    exact ⟨x.toNat, by omega, y.toNat, by omega, by omega, by omega⟩

private def axisCuts (makeLine : Int → Line) (size : Nat) : List Line :=
  (List.range' 1 (size - 1)).map fun (k : Nat) => makeLine (k : Int)

private theorem axisCuts_nodup {mk : Int → Line}
    (hinj : ∀ {x y}, mk x = mk y → x = y) (size : Nat) :
    (axisCuts mk size).Nodup := by
  unfold axisCuts List.Nodup
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_range' 1)
  intro i j h he
  have hk := hinj he
  omega

private theorem mem_axisCuts {mk : Int → Line}
    (hinj : ∀ {x y}, mk x = mk y → x = y) {size : Nat} {k : Int} :
    mk k ∈ axisCuts mk size ↔ 0 < k ∧ k < size := by
  simp only [axisCuts, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨hi, his⟩, he⟩
    have hk := hinj he
    omega
  · rintro ⟨hk, hks⟩
    exact ⟨k.toNat, ⟨by omega, by omega⟩, congrArg mk (by omega)⟩

/-- The rectangular case of `thm:min-dissection-path`. -/
theorem rectangle_minimum_cuts (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (internalLines (rectangle a b)).length = (a - 1) + (b - 1) := by
  let vertical := axisCuts Line.vertical a
  let horizontal := axisCuts Line.horizontal b
  let cuts := vertical ++ horizontal
  have hdisjoint : ∀ x ∈ vertical, ∀ y ∈ horizontal, x ≠ y := by
    intro x hx y hy
    simp only [vertical, horizontal, axisCuts, List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    intro h
    cases h
  have hd : cuts.Nodup := by
    simp only [cuts, List.Nodup, List.pairwise_append]
    exact ⟨axisCuts_nodup Line.vertical.inj a, axisCuts_nodup Line.horizontal.inj b, hdisjoint⟩
  have hlen : cuts.length = (a - 1) + (b - 1) := by
    simp [cuts, vertical, horizontal, axisCuts]
  have hs : Separates (rectangle a b) cuts := by
    rintro ⟨x, y⟩ hp
    have hp' := mem_rectangle.mp hp
    constructor
    · intro hq
      have hq' := mem_rectangle.mp hq
      exact List.mem_append_left _ ((mem_axisCuts Line.vertical.inj).2 (by omega))
    · intro hq
      have hq' := mem_rectangle.mp hq
      exact List.mem_append_right _ ((mem_axisCuts Line.horizontal.inj).2 (by omega))
  have hl := (minimum_cuts (rectangle a b)).2 cuts hs
  rw [hlen] at hl
  obtain ⟨minimal, hminimal, hlength⟩ := (minimum_cuts (rectangle a b)).1
  have hr : ∀ l ∈ cuts, l ∈ minimal := by
    intro l hl
    rcases List.mem_append.mp hl with hv | hh
    · simp only [vertical, axisCuts, List.mem_map] at hv
      obtain ⟨k, hk, rfl⟩ := hv
      have hk' := List.mem_range'_1.mp hk
      have hside := (hminimal ((k : Int) - 1, 0) (mem_rectangle.mpr (by omega))).1
      exact hside (mem_rectangle.mpr (by omega)) |> fun h => by simpa using h
    · simp only [horizontal, axisCuts, List.mem_map] at hh
      obtain ⟨k, hk, rfl⟩ := hh
      have hk' := List.mem_range'_1.mp hk
      have hside := (hminimal (0, (k : Int) - 1) (mem_rectangle.mpr (by omega))).2
      exact hside (mem_rectangle.mpr (by omega)) |> fun h => by simpa using h
  have hle := FiniteList.nodup_length_le_of_subset hd hr
  omega

end Thesis.Polyomino
