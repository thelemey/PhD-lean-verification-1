import Thesis.VanDerCorput
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp

open Filter Topology Finset
open scoped BigOperators

namespace Thesis.VanDerCorput

noncomputable def mean (u : Nat → ℂ) (N : Nat) : ℂ :=
  (N : ℝ)⁻¹ • ∑ n ∈ range N, u n

noncomputable def normalizedCorrelation (u : Nat → ℂ) (N r : Nat) : ℂ :=
  (N : ℝ)⁻¹ • correlation u N r

noncomputable def correlationBound (τ : ℝ) (r : Nat) : ℝ :=
  1 / Real.sqrt (1 + (τ * (r : ℝ)) ^ 2)

private noncomputable def windowBound (u : Nat → ℂ) (N H : Nat) : ℝ :=
  ((N + H - 1 : Nat) : ℝ) / N *
    ((H : ℝ)⁻¹ + (2 / (H : ℝ) ^ 2) * ∑ r ∈ range (H - 1),
      ((H - (r + 1) : Nat) : ℝ) * ‖normalizedCorrelation u N (r + 1)‖)

private noncomputable def limitBound (τ : ℝ) (H : Nat) : ℝ :=
  (H : ℝ)⁻¹ + (2 / (H : ℝ) ^ 2) *
    ∑ r ∈ range (H - 1), ((H - (r + 1) : Nat) : ℝ) * correlationBound τ (r + 1)

/-- The normalized estimate in the proof of `lem:logfact`, after bounding
each real part by the norm of its correlation. -/
theorem mean_sq_le (u : Nat → ℂ) (hu : ∀ n, ‖u n‖ = 1) (N H : Nat)
    (hN : 0 < N) (hH : 0 < H) :
    ‖mean u N‖ ^ 2 ≤ windowBound u N H := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (0 : ℝ) < H := by exact_mod_cast hH
  let C : ℝ := ∑ r ∈ range (H - 1),
    ((H - (r + 1) : Nat) : ℝ) * ‖correlation u N (r + 1)‖
  have hnorm : ∑ r ∈ range (H - 1),
      ((H - (r + 1) : Nat) : ℝ) * (correlation u N (r + 1)).re ≤ C := by
    apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (Nat.cast_nonneg _)
  have hraw := (finite_shift_square u hu N H).trans
    (mul_le_mul_of_nonneg_left (show (H : ℝ) * N +
      2 * (∑ r ∈ range (H - 1),
        ((H - (r + 1) : Nat) : ℝ) * (correlation u N (r + 1)).re) ≤
        (H : ℝ) * N + 2 * C by linarith)
      (Nat.cast_nonneg _))
  have hscale : ∑ r ∈ range (H - 1),
      ((H - (r + 1) : Nat) : ℝ) * ‖normalizedCorrelation u N (r + 1)‖ =
      (N : ℝ)⁻¹ * C := by
    unfold normalizedCorrelation C
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
    ring
  calc
    _ = ((H : ℝ) ^ 2 * ‖∑ n ∈ range N, u n‖ ^ 2) / ((H : ℝ) ^ 2 * (N : ℝ) ^ 2) := by
      rw [mean, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
      field_simp [hn.ne', hh.ne']
      ring
    _ ≤ (((N + H - 1 : Nat) : ℝ) * ((H : ℝ) * N + 2 * C)) /
        ((H : ℝ) ^ 2 * (N : ℝ) ^ 2) := div_le_div_of_nonneg_right hraw (by positivity)
    _ = _ := by
      rw [windowBound, hscale]
      field_simp [hn.ne', hh.ne']
      ring

private theorem window_factor_limit (H : Nat) (hH : 0 < H) :
    Tendsto (fun N : Nat => ((N + H - 1 : Nat) : ℝ) / N) atTop (𝓝 1) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat ((H - 1 : Nat) : ℝ)).const_add 1
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hn
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [show N + H - 1 = N + (H - 1) by omega, Nat.cast_add, add_div, div_self hN]

private theorem windowBound_tendsto (u : Nat → ℂ) (τ : ℝ) (H : Nat) (hH : 0 < H)
    (hcorr : ∀ r > 0, Tendsto (fun N : Nat => ‖normalizedCorrelation u N r‖)
      atTop (𝓝 (correlationBound τ r))) :
    Tendsto (fun N => windowBound u N H) atTop (𝓝 (limitBound τ H)) := by
  have hs : Tendsto (fun N : Nat => ∑ r ∈ range (H - 1),
        ((H - (r + 1) : Nat) : ℝ) * ‖normalizedCorrelation u N (r + 1)‖) atTop
      (𝓝 (∑ r ∈ range (H - 1), ((H - (r + 1) : Nat) : ℝ) * correlationBound τ (r + 1))) := by
    apply tendsto_finset_sum
    intro r _
    exact (hcorr (r + 1) (by omega)).const_mul _
  have hs' := (hs.const_mul (2 / (H : ℝ) ^ 2)).const_add (H : ℝ)⁻¹
  simpa only [windowBound, limitBound, one_mul] using (window_factor_limit H hH).mul hs'

private theorem correlation_bound_le_inverse (τ : ℝ) (hτ : τ ≠ 0) (r : Nat) (hr : 0 < r) :
    correlationBound τ r ≤ |τ|⁻¹ * (r : ℝ)⁻¹ := by
  have hτ' : 0 < |τ| := abs_pos.mpr hτ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs : |τ| * (r : ℝ) ≤ Real.sqrt (1 + (τ * (r : ℝ)) ^ 2) := by
    have hab : |τ * (r : ℝ)| = |τ| * (r : ℝ) := by rw [abs_mul, abs_of_pos hr']
    rw [← hab, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  unfold correlationBound
  rw [← mul_inv, ← one_div]
  exact one_div_le_one_div_of_le (mul_pos hτ' hr') hs

private noncomputable def harmonicBound (τ : ℝ) (H : Nat) : ℝ :=
  (H : ℝ)⁻¹ + 2 * |τ|⁻¹ * ((H : ℝ)⁻¹ * ∑ r ∈ range (H - 1), ((r + 1 : Nat) : ℝ)⁻¹)

private theorem limitBound_le_harmonic (τ : ℝ) (hτ : τ ≠ 0) (H : Nat) :
    limitBound τ H ≤ harmonicBound τ H := by
  by_cases hz : H = 0
  · subst H
    simp [limitBound, harmonicBound]
  have hH : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hsum :
      (∑ r ∈ range (H - 1), ((H - (r + 1) : Nat) : ℝ) * correlationBound τ (r + 1)) ≤
      ((H : ℝ) * |τ|⁻¹) * ∑ r ∈ range (H - 1), ((r + 1 : Nat) : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    rw [mul_assoc]
    exact mul_le_mul (by exact_mod_cast Nat.sub_le H (r + 1))
      (correlation_bound_le_inverse τ hτ (r + 1) (by omega))
      (by unfold correlationBound; positivity) hH.le
  unfold limitBound harmonicBound
  calc
    _ ≤ (H : ℝ)⁻¹ + 2 / (H : ℝ) ^ 2 *
        (((H : ℝ) * |τ|⁻¹) * ∑ r ∈ range (H - 1), ((r + 1 : Nat) : ℝ)⁻¹) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hsum (by positivity)) _
    _ = _ := by field_simp [hH.ne']; ring

private theorem harmonicBound_tendsto (τ : ℝ) :
    Tendsto (harmonicBound τ) atTop (𝓝 0) := by
  have hterm : Tendsto (fun r : Nat => ((r + 1 : Nat) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have hfirst : Tendsto (fun H : Nat => (H : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_atTop_nhds_zero_nat
  have hpartial : Tendsto (fun H : Nat =>
      (H : ℝ)⁻¹ * ∑ r ∈ range (H - 1), ((r + 1 : Nat) : ℝ)⁻¹) atTop (𝓝 0) := by
    refine squeeze_zero ?_ ?_ hterm.cesaro
    · intro H
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
    · intro H
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega)
      · exact fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  simpa only [harmonicBound, mul_zero, add_zero] using hfirst.add
    (hpartial.const_mul (2 * |τ|⁻¹))

private theorem limitBound_tendsto (τ : ℝ) (hτ : τ ≠ 0) :
    Tendsto (limitBound τ) atTop (𝓝 0) :=
  squeeze_zero (by
    intro H
    unfold limitBound
    apply add_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
    exact Finset.sum_nonneg (fun r _ => mul_nonneg (Nat.cast_nonneg _)
      (by unfold correlationBound; positivity)))
    (limitBound_le_harmonic τ hτ) (harmonicBound_tendsto τ)

/-- The two-limit argument of `lem:logfact`: keep the window length fixed
while taking the segment-length limit, then let the window length grow. -/
theorem mean_tendsto_zero (u : Nat → ℂ) (hu : ∀ n, ‖u n‖ = 1)
    (τ : ℝ) (hτ : τ ≠ 0)
    (hcorr : ∀ r > 0, Tendsto (fun N : Nat => ‖normalizedCorrelation u N r‖)
      atTop (𝓝 (correlationBound τ r))) :
    Tendsto (mean u) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hε2 : 0 < ε ^ 2 := by positivity
  have hsmall : ∀ᶠ H in atTop, limitBound τ H < ε ^ 2 :=
    (limitBound_tendsto τ hτ).eventually (gt_mem_nhds hε2)
  have hpositive : ∀ᶠ H : Nat in atTop, 0 < H := eventually_gt_atTop 0
  obtain ⟨H, hH, hlim⟩ := (hpositive.and hsmall).exists
  have hev : ∀ᶠ N : Nat in atTop, windowBound u N H < ε ^ 2 :=
    (windowBound_tendsto u τ H hH hcorr).eventually (gt_mem_nhds hlim)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨max K 1, ?_⟩
  intro N hN
  have hN0 : 0 < N := by omega
  have hb := (mean_sq_le u hu N H hN0 hH).trans_lt (hK N (by omega))
  rw [dist_zero_right]
  by_contra hh
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le (le_of_not_gt hh) 2)) hb

/-- Passing from a correlation divided by its own number of terms (M)
to the thesis's normalization by the full segment length (N=M+r). -/
theorem normalizedCorrelation_tendsto_of_short_mean (u : Nat → ℂ) (r : Nat) (L : ℝ)
    (h : Tendsto (fun M : Nat =>
      ‖(M : ℝ)⁻¹ • (∑ n ∈ range M, u (n + r) * (starRingEnd ℂ) (u n))‖)
      atTop (𝓝 L)) :
    Tendsto (fun N : Nat => ‖normalizedCorrelation u N r‖) atTop (𝓝 L) := by
  have hshort := h.comp (tendsto_sub_atTop_nat r)
  have hratio : Tendsto (fun N : Nat => ((N - r : Nat) : ℝ) / N) atTop (𝓝 1) := by
    have hr := (tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)).const_sub 1
    rw [sub_zero] at hr
    refine hr.congr' ?_
    filter_upwards [eventually_gt_atTop r] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [Nat.cast_sub hN.le, sub_div, div_self hn]
  have hprod := hratio.mul hshort
  rw [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop r] with N hN
  have hM : (0 : ℝ) < ((N - r : Nat) : ℝ) := by exact_mod_cast (show 0 < N - r by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp only [Function.comp_def, normalizedCorrelation, correlation, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hM.le), abs_of_nonneg (inv_nonneg.mpr hNr.le)]
  field_simp [hM.ne', hNr.ne']
  ring

end Thesis.VanDerCorput
