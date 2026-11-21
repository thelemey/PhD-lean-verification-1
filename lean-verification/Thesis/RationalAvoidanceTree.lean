import Thesis.NestedIntervalCodes
import Thesis.RationalAvoidanceIntervals
import Thesis.SturmianDensityMeasure
import Mathlib.Data.Nat.Log

open Set Metric Filter
open scoped Topology

namespace Thesis.SturmianDensity.Avoidance

open NestedIntervals

variable {S B : ℕ}

noncomputable def candidate (S n : ℕ) (x : ℝ) (j : Fin (B + 1)) : ℝ :=
  x + 2 * j.val * width S (n + 1)

theorem candidate_bounds (hS : 1 < S) (hSB : S ^ 2 = 2 * (B + 1))
    (n : ℕ) (x : ℝ) (j : Fin (B + 1)) :
    x ≤ candidate S n x j ∧ candidate S n x j + width S (n + 1) ≤ x + width S n := by
  have hw := width_pos hS (n + 1)
  have hscale : scale S = 2 * ((B : ℝ) + 1) := by
    unfold scale
    exact_mod_cast hSB
  have hj : (j.val : ℝ) + 1 ≤ (B : ℝ) + 1 := by
    exact_mod_cast j.isLt
  have h := mul_le_mul_of_nonneg_right hj hw.le
  unfold candidate
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · rw [← width_step hS n, hscale]
    linarith

theorem candidate_separation (hS : 1 < S) (n : ℕ) (x : ℝ)
    {i j : Fin (B + 1)} (hij : i ≠ j) :
    2 * width S (n + 1) ≤ dist (candidate S n x i) (candidate S n x j) := by
  have hw := width_pos hS (n + 1)
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rw [Real.dist_eq]
  unfold candidate
  rcases lt_or_gt_of_ne hne with h | h
  · have hi : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
    have hb := mul_le_mul_of_nonneg_right hi hw.le
    apply le_trans _ (neg_le_abs _)
    linarith
  · have hi : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast h
    have hb := mul_le_mul_of_nonneg_right hi hw.le
    apply le_trans _ (le_abs_self _)
    linarith

def badCandidate (S n : ℕ) (x : ℝ) (j : Fin (B + 1)) : Prop :=
  ∃ (p : ℤ) (q : ℕ), S ^ n ≤ q ∧ q < S ^ (n + 1) ∧
    ∃ y ∈ Icc (candidate S n x j) (candidate S n x j + width S (n + 1)),
      |y - (p : ℝ) / q| < margin S n

theorem badCandidate_unique (hS : 1 < S) (hSB : S ^ 2 = 2 * (B + 1)) (n : ℕ) (x : ℝ)
    {i j : Fin (B + 1)} (hi : badCandidate S n x i) (hj : badCandidate S n x j) : i = j := by
  by_contra hne
  obtain ⟨p, q, hq, hQ, y, ⟨hyl, hyr⟩, hy⟩ := hi
  obtain ⟨p', q', hq', hQ', z, ⟨hzl, hzr⟩, hz⟩ := hj
  obtain ⟨hil, hir⟩ := candidate_bounds hS hSB n x i
  obtain ⟨hjl, hjr⟩ := candidate_bounds hS hSB n x j
  have center_mem {y a : ℝ} (hyl : x ≤ y) (hyr : y ≤ x + width S n)
      (hy : |y - a| < margin S n) :
      a ∈ Icc (x - margin S n) (x + width S n + margin S n) := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hy
    exact ⟨by linarith only [hyl, hhi], by linarith only [hyr, hlo]⟩
  have hcenter := dangerous_centers_eq hS n x hq hq' hQ hQ'
    (center_mem (hil.trans hyl) (hyr.trans hir) hy)
    (center_mem (hjl.trans hzl) (hzr.trans hjr) hz)
  have hnear : |y - z| < 2 * margin S n := by
    rw [← hcenter] at hz
    calc
      |y - z| ≤ |y - (p : ℝ) / q| + |(p : ℝ) / q - z| := abs_sub_le _ _ _
      _ < 2 * margin S n := by
        rw [abs_sub_comm ((p : ℝ) / q) z, two_mul]
        exact add_lt_add hy hz
  have hsep := candidate_separation hS n x hne
  rw [Real.dist_eq] at hsep
  have hw := width_pos hS (n + 1)
  have hm : 2 * margin S n = width S (n + 1) / 2 := by unfold margin; ring
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hnear
  rcases le_total (candidate S n x i) (candidate S n x j) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hsep
    linarith only [hsep, hyr, hzl, hlo, hw, hm]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hsep
    linarith only [hsep, hyl, hzr, hhi, hw, hm]

theorem exists_safeChildren (hS : 1 < S) (hSB : S ^ 2 = 2 * (B + 1)) (n : ℕ) (x : ℝ) :
    ∃ e : Fin B ↪ Fin (B + 1), ∀ j, ¬ badCandidate S n x (e j) := by
  classical
  by_cases h : ∃ j : Fin (B + 1), badCandidate S n x j
  · obtain ⟨i, hi⟩ := h
    refine ⟨Fin.succAboveEmb i, fun j hj => ?_⟩
    exact Fin.succAbove_ne i j (badCandidate_unique hS hSB n x hj hi)
  · exact ⟨Fin.succAboveEmb (Fin.last B), fun j hj => h ⟨_, hj⟩⟩

noncomputable def selected (hS : 1 < S) (hSB : S ^ 2 = 2 * (B + 1)) (n : ℕ) (x : ℝ) :
    Fin B ↪ Fin (B + 1) :=
  (exists_safeChildren hS hSB n x).choose

theorem selected_safe (hS : 1 < S) (hSB : S ^ 2 = 2 * (B + 1)) (n : ℕ) (x : ℝ)
    (j : Fin B) : ¬ badCandidate S n x (selected hS hSB n x j) :=
  (exists_safeChildren hS hSB n x).choose_spec j

theorem width_zero (hS : 1 < S) : Tendsto (width S) atTop (𝓝 0) := by
  have hscale := scale_gt_one hS
  have hp : 0 < scale S := zero_lt_one.trans hscale
  have hz := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hp.le)
    (inv_lt_one_of_one_lt₀ hscale)
  convert hz.const_mul (1 / (4 * scale S)) using 1
  · funext n
    rw [width, pow_succ', ← mul_assoc, ← div_div, inv_pow, div_eq_mul_inv (1 / (4 * scale S))]
  · simp

noncomputable def code (hS : 1 < S) (hSB : S ^ 2 = 2 * (B + 1)) : IntervalCode B where
  origin := 1 / 4
  width := width S
  width_pos := width_pos hS
  width_zero := width_zero hS
  child n x j := candidate S n x (selected hS hSB n x j)
  child_bounds n x j := candidate_bounds hS hSB n x (selected hS hSB n x j)

theorem code_separation (hS : 1 < S) (hSB : S ^ 2 = 2 * (B + 1))
    (n : ℕ) (x : ℝ) (i j : Fin B) (hij : i ≠ j) :
    2 * (code hS hSB).width (n + 1) ≤ dist ((code hS hSB).child n x i) ((code hS hSB).child n x j) :=
  candidate_separation hS n x (fun h => hij ((selected hS hSB n x).injective h))

theorem range_code_subset (hS : 1 < S) (hSB : S ^ 2 = 2 * (B + 1)) :
    range (code hS hSB).point ⊆ badlyApproximableSlopes := by
  rintro x ⟨v, rfl⟩
  let T := code hS hSB
  have hzero : T.width 0 < 1 / 4 := by
    change width S 0 < _
    simp only [width, zero_add, pow_one]
    exact one_div_lt_one_div_of_lt (by norm_num) (by linarith [scale_gt_one hS])
  obtain ⟨hl, hr⟩ := T.point_mem_interval v 0
  change 1 / 4 ≤ T.point v at hl
  change T.point v ≤ 1 / 4 + T.width 0 at hr
  refine ⟨⟨by linarith, by linarith⟩, constant S, constant_pos hS, ?_⟩
  intro p q hq
  let n := Nat.log S q
  have hlow : S ^ n ≤ q := Nat.pow_log_le_self S hq.ne'
  have hhigh : q < S ^ (n + 1) := Nat.lt_pow_succ_log_self hS q
  by_contra! h
  have hm := band_error_le_margin hS n q hlow
  have hmem := T.point_mem_interval v (n + 1)
  change T.point v ∈ Icc (candidate S n (T.start v n) (selected hS hSB n (T.start v n) (v n)))
    (candidate S n (T.start v n) (selected hS hSB n (T.start v n) (v n)) + width S (n + 1)) at hmem
  exact selected_safe hS hSB n (T.start v n) (v n)
    ⟨p, q, hlow, hhigh, T.point v, hmem, h.trans_le hm⟩

end Thesis.SturmianDensity.Avoidance
