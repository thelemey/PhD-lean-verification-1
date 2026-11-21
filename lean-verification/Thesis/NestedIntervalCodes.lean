import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

open Set Filter Metric
open scoped Topology

namespace Thesis.NestedIntervals

/-- An interval at each level and an indexed choice of subintervals. -/
structure IntervalCode (B : ℕ) where
  origin : ℝ
  width : ℕ → ℝ
  width_pos : ∀ n, 0 < width n
  width_zero : Tendsto width atTop (𝓝 0)
  child : ℕ → ℝ → Fin B → ℝ
  child_bounds : ∀ n x j, x ≤ child n x j ∧ child n x j + width (n + 1) ≤ x + width n

namespace IntervalCode

variable {B : ℕ}

def start (T : IntervalCode B) (v : ℕ → Fin B) : ℕ → ℝ
  | 0 => T.origin
  | n + 1 => T.child n (T.start v n) (v n)

def interval (T : IntervalCode B) (v : ℕ → Fin B) (n : ℕ) : Set ℝ :=
  Icc (T.start v n) (T.start v n + T.width n)

theorem start_mono (T : IntervalCode B) (v : ℕ → Fin B) : Monotone (T.start v) :=
  monotone_nat_of_le_succ fun n => (T.child_bounds n (T.start v n) (v n)).1

theorem right_anti (T : IntervalCode B) (v : ℕ → Fin B) :
    Antitone (fun n => T.start v n + T.width n) :=
  antitone_nat_of_succ_le fun n => (T.child_bounds n (T.start v n) (v n)).2

theorem start_le_right (T : IntervalCode B) (v : ℕ → Fin B) (m n : ℕ) :
    T.start v m ≤ T.start v n + T.width n := by
  rcases le_total m n with hm | hn
  · exact (T.start_mono v hm).trans (le_add_of_nonneg_right (T.width_pos n).le)
  · exact (le_add_of_nonneg_right (T.width_pos m).le).trans (T.right_anti v hn)

/-- The point picked by an infinite sequence of child labels. -/
noncomputable def point (T : IntervalCode B) (v : ℕ → Fin B) : ℝ :=
  sSup (range (T.start v))

theorem point_mem_interval (T : IntervalCode B) (v : ℕ → Fin B) (n : ℕ) :
    T.point v ∈ T.interval v n := by
  have hb : BddAbove (range (T.start v)) :=
    ⟨T.start v n + T.width n, fun _ ⟨m, hm⟩ => hm ▸ T.start_le_right v m n⟩
  exact ⟨le_csSup hb ⟨n, rfl⟩, csSup_le (range_nonempty _) (fun _ ⟨m, hm⟩ =>
    hm ▸ T.start_le_right v m n)⟩

theorem point_eq_of_mem_all (T : IntervalCode B) (v : ℕ → Fin B) (x : ℝ)
    (hx : ∀ n, x ∈ T.interval v n) : T.point v = x := by
  have ha (n : ℕ) : |T.point v - x| ≤ T.width n := by
    obtain ⟨h₁, h₂⟩ := T.point_mem_interval v n
    obtain ⟨h₃, h₄⟩ := hx n
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h := le_of_tendsto_of_tendsto tendsto_const_nhds T.width_zero (Eventually.of_forall ha)
  exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm h (abs_nonneg _)))

theorem start_eq_of_agreement (T : IntervalCode B) {v w : ℕ → Fin B} {n : ℕ}
    (h : ∀ j < n, v j = w j) : T.start v n = T.start w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T.child n (T.start v n) (v n) = T.child n (T.start w n) (w n)
    rw [ih (fun j hj => h j (hj.trans (Nat.lt_succ_self _))), h n (Nat.lt_succ_self _)]

/-- With every child interval available, any point of the initial
interval has an address. Closed intervals allow endpoint addresses. -/
theorem exists_address (T : IntervalCode B)
    (hcover : ∀ n x y, y ∈ Icc x (x + T.width n) →
      ∃ i, y ∈ Icc (T.child n x i) (T.child n x i + T.width (n + 1)))
    {y : ℝ} (hy : y ∈ Icc T.origin (T.origin + T.width 0)) :
    ∃ v : ℕ → Fin B, T.point v = y := by
  classical
  let step (n : ℕ) (x : {x : ℝ // y ∈ Icc x (x + T.width n)}) : Fin B :=
    (hcover n x.val y x.property).choose
  let loc : ∀ n : ℕ, {x : ℝ // y ∈ Icc x (x + T.width n)} :=
    Nat.rec ⟨T.origin, hy⟩ fun n x =>
      ⟨T.child n x.val (step n x), (hcover n x.val y x.property).choose_spec⟩
  let path := fun n => step n (loc n)
  have he (n : ℕ) : T.start path n = (loc n).val := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change T.child n (T.start path n) (path n) = T.child n (loc n).val (path n)
      rw [ih]
  refine ⟨path, T.point_eq_of_mem_all path y fun n => ?_⟩
  unfold interval
  rw [he]
  exact (loc n).property

theorem point_dist_le_of_agreement (T : IntervalCode B) {v w : ℕ → Fin B} {n : ℕ}
    (h : ∀ j < n, v j = w j) : dist (T.point v) (T.point w) ≤ T.width n := by
  obtain ⟨h₁, h₂⟩ := T.point_mem_interval v n
  obtain ⟨h₃, h₄⟩ := T.point_mem_interval w n
  have hs := T.start_eq_of_agreement h
  change T.start v n ≤ T.point v at h₁
  change T.point v ≤ T.start v n + T.width n at h₂
  change T.start w n ≤ T.point w at h₃
  change T.point w ≤ T.start w n + T.width n at h₄
  rw [Real.dist_eq]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Separation at the first differing label forces the source points
to remain apart by at least the length of that child interval. -/
theorem point_dist_ge_of_separation (T : IntervalCode B)
    (hsep : ∀ n x i j, i ≠ j → 2 * T.width (n + 1) ≤ dist (T.child n x i) (T.child n x j))
    {v w : ℕ → Fin B} {n : ℕ} (h : ∀ j < n, v j = w j) (hn : v n ≠ w n) :
    T.width (n + 1) ≤ dist (T.point v) (T.point w) := by
  have hs := T.start_eq_of_agreement h
  have hsize : 2 * T.width (n + 1) ≤ dist (T.start v (n + 1)) (T.start w (n + 1)) := by
    change _ ≤ dist (T.child n (T.start v n) (v n)) (T.child n (T.start w n) (w n))
    rw [← hs]
    exact hsep n _ _ _ hn
  obtain ⟨h₁, h₂⟩ := T.point_mem_interval v (n + 1)
  obtain ⟨h₃, h₄⟩ := T.point_mem_interval w (n + 1)
  change T.start v (n + 1) ≤ T.point v at h₁
  change T.point v ≤ T.start v (n + 1) + T.width (n + 1) at h₂
  change T.start w (n + 1) ≤ T.point w at h₃
  change T.point w ≤ T.start w (n + 1) + T.width (n + 1) at h₄
  rw [Real.dist_eq] at hsize ⊢
  rcases le_total (T.start v (n + 1)) (T.start w (n + 1)) with hl | hr
  · rw [abs_of_nonpos (sub_nonpos.mpr hl)] at hsize
    have hle : T.width (n + 1) ≤ T.point w - T.point v := by linarith
    linarith [neg_le_abs (T.point v - T.point w)]
  · rw [abs_of_nonneg (sub_nonneg.mpr hr)] at hsize
    have hle : T.width (n + 1) ≤ T.point v - T.point w := by linarith
    exact hle.trans (le_abs_self _)

end IntervalCode
end Thesis.NestedIntervals
