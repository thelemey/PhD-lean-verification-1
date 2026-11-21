import Thesis.PolyominoGeometry
import Mathlib.Topology.MetricSpace.Pseudo.Pi

open Set

namespace Thesis.Polyomino

theorem cellCenter_mem_interior {cells : List Cell} (p : CellIn cells) :
    cellCenter p.val ∈ interior (remaining cells []) := by
  let U := ⋂ a : Bool, (fun z : Plane => z a) ⁻¹'
    Ioo (axisCoord p.val a : ℝ) ((axisCoord p.val a : ℝ) + 1)
  have ho : IsOpen U :=
    isOpen_iInter_of_finite fun a => isOpen_Ioo.preimage (continuous_apply a)
  have hsub : U ⊆ remaining cells [] := by
    intro z hz
    exact ⟨⟨p, fun a => ⟨(mem_iInter.1 hz a).1.le, (mem_iInter.1 hz a).2.le⟩⟩, by simp⟩
  apply interior_maximal hsub ho
  apply mem_iInter.2
  intro a
  change (axisCoord p.val a : ℝ) < (axisCoord p.val a : ℝ) + 1 / 2 ∧
    (axisCoord p.val a : ℝ) + 1 / 2 < (axisCoord p.val a : ℝ) + 1
  constructor <;> linarith

private theorem cell_coord_unique {j k : ℤ} {x : ℝ}
    (hx : x ∈ Ioo (k : ℝ) ((k : ℝ) + 1)) (hj : x ∈ Icc (j : ℝ) ((j : ℝ) + 1)) :
    j = k := by
  have h₁ : j < k + 1 := by exact_mod_cast hj.1.trans_lt hx.2
  have h₂ : k < j + 1 := by exact_mod_cast hx.1.trans_le hj.2
  omega

/-- At an interior point on a grid line, a small ball contains points on
both sides with the same transverse, nonintegral coordinate. The two
covering squares therefore have a full common side on that line. -/
theorem sharedSide_of_interior_point {cells : List Cell} {z : Plane}
    (hz : z ∈ interior (remaining cells [])) (a : Bool) (c : ℤ) (hc : z a = c) :
    ∃ p q : CellIn cells, SharedSide p.val q.val (axisLine a c) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
  let y := z (!a)
  let k := ⌊y⌋
  have hyl : (k : ℝ) ≤ y := Int.floor_le y
  have hyu : y < (k : ℝ) + 1 := Int.lt_floor_add_one y
  let δ := min (ε/2) (min (1/2) (((k : ℝ) + 1 - y)/2))
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by norm_num) (by linarith))
  have hδe : δ ≤ ε/2 := min_le_left _ _
  have hδ1 : δ ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδy : δ ≤ ((k : ℝ)+1-y)/2 := (min_le_right _ _).trans (min_le_right _ _)
  let point (s : ℝ) : Plane := fun d => if d = a then (c : ℝ) + s else y + δ
  have inBall (s : ℝ) (hs : |s| ≤ δ) : point s ∈ Metric.ball z ε := by
    apply (dist_pi_lt_iff hε).2
    intro d
    by_cases hd : d = a
    · subst d
      simpa [point, hc, Real.dist_eq] using hs.trans_lt (show δ < ε by linarith)
    · have he : d = !a := by cases d <;> cases a <;> simp_all
      have hz' : z d = y := congrArg z he
      simp only [point, hd, if_false, hz', Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ]
      linarith
  obtain ⟨p, hp⟩ := (hball (inBall (-δ) (by simp [abs_of_pos hδ]))).1
  obtain ⟨q, hq⟩ := (hball (inBall δ (by simp [abs_of_pos hδ]))).1
  have hpa : axisCoord p.val a = c - 1 := by
    apply cell_coord_unique (x := point (-δ) a) _ (hp a)
    simp only [point, if_true, Int.cast_sub, Int.cast_one, mem_Ioo]
    constructor <;> linarith
  have hqa : axisCoord q.val a = c := by
    apply cell_coord_unique (x := point δ a) _ (hq a)
    simp only [point, if_true, mem_Ioo]
    constructor <;> linarith
  have htrans (s : ℝ) : point s (!a) ∈ Ioo (k : ℝ) ((k : ℝ) + 1) := by
    have ha : (!a) ≠ a := by cases a <;> decide
    simp only [point, ha, if_false, mem_Ioo]
    constructor <;> linarith
  have hpb := cell_coord_unique (htrans (-δ)) (hp (!a))
  have hqb := cell_coord_unique (htrans δ) (hq (!a))
  refine ⟨p, q, Or.inl ?_⟩
  cases a
  · apply Or.inl
    simp [axisCoord] at hpa hqa hpb hqb
    exact ⟨Prod.ext (by dsimp; omega) (by dsimp; omega), by simp [axisLine, hpa]⟩
  · apply Or.inr
    simp [axisCoord] at hpa hqa hpb hqb
    exact ⟨Prod.ext (by dsimp; omega) (by dsimp; omega), by simp [axisLine, hpa]⟩

/-- The crossing step in §4.2 with “inside” interpreted as the topological
interior. Connectedness and the intermediate value property suffice. -/
theorem sharedSide_of_preconnected_interior {cells : List Cell}
    (h : IsPreconnected (interior (remaining cells []))) (u v : CellIn cells)
    (a : Bool) (c : ℤ) (hlo : axisCoord u.val a < c) (hhi : c ≤ axisCoord v.val a) :
    ∃ p q : CellIn cells, SharedSide p.val q.val (axisLine a c) := by
  have hl : (axisCoord u.val a : ℝ) + 1 ≤ c := by
    exact_mod_cast (show axisCoord u.val a + 1 ≤ c by omega)
  have hh : (c : ℝ) ≤ axisCoord v.val a := by exact_mod_cast hhi
  have hc : (c : ℝ) ∈ Icc (cellCenter u.val a) (cellCenter v.val a) := by
    simp only [cellCenter, mem_Icc]
    constructor <;> linarith
  obtain ⟨z, hz, he⟩ := h.intermediate_value (cellCenter_mem_interior u)
    (cellCenter_mem_interior v) (continuous_apply a).continuousOn hc
  exact sharedSide_of_interior_point hz a c he

/-- The minimum counts distinct internal grid lines. The pieces in this
formulation are the connected components of the actual geometric remainder. -/
theorem minimum_geometric_cuts_of_preconnected_interior {cells : List Cell}
    (h : IsPreconnected (interior (remaining cells []))) :
    (∃ cuts, GeometricallySeparated cells cuts ∧ cuts.length = (internalLines cells).length) ∧
    ∀ cuts, GeometricallySeparated cells cuts → (internalLines cells).length ≤ cuts.length := by
  simpa only [geometricallySeparated_iff_of_crossings (sharedSide_of_preconnected_interior h)] using
    minimum_cuts cells

end Thesis.Polyomino
