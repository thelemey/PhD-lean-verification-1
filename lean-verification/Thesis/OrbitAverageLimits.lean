import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology BigOperators ENNReal

namespace Thesis.OrbitAverages

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

private noncomputable def compactMap (f : C(X, ℝ)) : C_c(X, ℝ) :=
  ⟨f, HasCompactSupport.of_compactSpace f⟩

omit [TopologicalSpace X] [CompactSpace X] in
private theorem average_eq (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    birkhoffAverage ℝ T f n x = (∑ j ∈ Finset.range n, f (T^[j] x)) / (n : ℝ) := by
  simp [birkhoffAverage, birkhoffSum, div_eq_mul_inv, mul_comm]

private theorem abs_average_le (T : X → X) (f : C_c(X, ℝ)) (x : X) (n : ℕ) :
    |birkhoffAverage ℝ T f n x| ≤ ‖f.toContinuousMap‖ := by
  rw [average_eq, abs_div, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    apply (div_le_iff₀ hn').2
    calc
      _ ≤ ∑ j ∈ Finset.range n, |f (T^[j] x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range n, ‖f.toContinuousMap‖ := by
        exact Finset.sum_le_sum fun j _ => f.toContinuousMap.norm_coe_le_norm (T^[j] x)
      _ = _ := by simp [nsmul_eq_mul, mul_comm]

private theorem averages_have_limit (T : X → X) (x : ℕ → X) (m : ℕ → ℕ)
    (U : Ultrafilter ℕ) (f : C_c(X, ℝ)) :
    ∃ y : ℝ, Tendsto (fun i => birkhoffAverage ℝ T f (m i) (x i)) (U : Filter ℕ) (𝓝 y) := by
  let a := fun i => birkhoffAverage ℝ T f (m i) (x i)
  let B := ‖f.toContinuousMap‖
  have h : Icc (-B) B ∈ U.map a := by
    change a ⁻¹' Icc (-B) B ∈ (U : Filter ℕ)
    exact Eventually.of_forall fun i => abs_le.mp (abs_average_le T f (x i) (m i))
  obtain ⟨y, _, hy⟩ := isCompact_Icc.ultrafilter_le_nhds' (U.map a) h
  exact ⟨y, hy⟩

private noncomputable def averageLimit (T : X → X) (x : ℕ → X) (m : ℕ → ℕ)
    (U : Ultrafilter ℕ) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := limUnder (U : Filter ℕ) (fun i => birkhoffAverage ℝ T f (m i) (x i))
  map_add' f g := by
    apply tendsto_nhds_unique (tendsto_nhds_limUnder (averages_have_limit T x m U (f + g)))
    refine ((tendsto_nhds_limUnder (averages_have_limit T x m U f)).add
      (tendsto_nhds_limUnder (averages_have_limit T x m U g))).congr ?_
    intro i
    simp [average_eq, Finset.sum_add_distrib, add_div]
  map_smul' c f := by
    apply tendsto_nhds_unique (tendsto_nhds_limUnder (averages_have_limit T x m U (c • f)))
    refine ((tendsto_nhds_limUnder (averages_have_limit T x m U f)).const_mul c).congr ?_
    intro i
    simp only [average_eq, coe_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]

private theorem tendsto_averageLimit (T : X → X) (x : ℕ → X) (m : ℕ → ℕ)
    (U : Ultrafilter ℕ) (f : C_c(X, ℝ)) :
    Tendsto (fun i => birkhoffAverage ℝ T f (m i) (x i)) (U : Filter ℕ)
      (𝓝 (averageLimit T x m U f)) :=
  tendsto_nhds_limUnder (averages_have_limit T x m U f)

private theorem averageLimit_nonneg (T : X → X) (x : ℕ → X) (m : ℕ → ℕ)
    (U : Ultrafilter ℕ) (f : C_c(X, ℝ)) (hf : 0 ≤ f) :
    0 ≤ averageLimit T x m U f := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_averageLimit T x m U f)
  filter_upwards [] with i
  rw [average_eq]
  exact div_nonneg (Finset.sum_nonneg fun j _ => hf (T^[j] (x i))) (Nat.cast_nonneg _)

private theorem averageLimit_const (T : X → X) (x : ℕ → X) (m : ℕ → ℕ) (U : Ultrafilter ℕ)
    (hm : ∀ᶠ i in (U : Filter ℕ), 0 < m i) :
    averageLimit T x m U (compactMap (ContinuousMap.const X 1)) = 1 := by
  apply tendsto_nhds_unique (tendsto_averageLimit T x m U _)
  apply tendsto_const_nhds.congr'
  filter_upwards [hm] with i hi
  simp [average_eq, compactMap, Nat.ne_of_gt hi]

private theorem averageLimit_comp (T : X → X) (hT : Continuous T)
    (x : ℕ → X) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (f : C(X, ℝ)) :
    averageLimit T x m U (compactMap (f.comp ⟨T, hT⟩)) =
      averageLimit T x m U (compactMap f) := by
  have hleft := tendsto_averageLimit T x m U (compactMap (f.comp ⟨T, hT⟩))
  have hright := tendsto_averageLimit T x m U (compactMap f)
  have hz : Tendsto (fun i => (m i : ℝ)⁻¹ * (2 * ‖f‖)) (U : Filter ℕ) (𝓝 0) := by
    have hc : Tendsto (fun i => (m i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
    have h := (tendsto_inv_atTop_zero.comp hc).mono_left hU
    simpa only [zero_mul] using h.mul_const (2 * ‖f‖)
  have hdiff : Tendsto (fun i => birkhoffAverage ℝ T (compactMap (f.comp ⟨T, hT⟩)) (m i) (x i) -
      birkhoffAverage ℝ T (compactMap f) (m i) (x i)) (U : Filter ℕ) (𝓝 0) := by
    refine squeeze_zero_norm (fun i => ?_) hz
    have hcomp : birkhoffAverage ℝ T (compactMap (f.comp ⟨T, hT⟩)) (m i) (x i) =
        birkhoffAverage ℝ T f (m i) (T (x i)) := by
      simp only [birkhoffAverage, birkhoffSum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      change f (T ((T^[j]) (x i))) = f ((T^[j]) (T (x i)))
      exact congrArg f ((Function.iterate_succ_apply' T j (x i)).symm.trans
        (Function.iterate_succ_apply T j (x i)))
    change ‖birkhoffAverage ℝ T (compactMap (f.comp ⟨T, hT⟩)) (m i) (x i) -
        birkhoffAverage ℝ T f (m i) (x i)‖ ≤ _
    rw [hcomp, birkhoffAverage_apply_sub_birkhoffAverage, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    calc
      _ ≤ ‖f ((T^[m i]) (x i))‖ + ‖f (x i)‖ := norm_sub_le _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      _ = _ := (two_mul _).symm
  exact sub_eq_zero.mp (tendsto_nhds_unique (hleft.sub hright) hdiff)

variable [T2Space X] [MeasurableSpace X] [BorelSpace X] [HasOuterApproxClosed X]

/-- Any ultralimit of long orbit averages on a compact space is given
by an invariant probability measure. The starting points may vary. -/
theorem invariant_limit_of_orbit_averages (T : X → X) (hT : Continuous T)
    (x : ℕ → X) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ MeasurePreserving T μ μ ∧
      ∀ f : C(X, ℝ), Tendsto (fun i => birkhoffAverage ℝ T f (m i) (x i)) (U : Filter ℕ)
        (𝓝 (∫ y, f y ∂μ)) := by
  let L := averageLimit T x m U
  let μ := RealRMK.rieszMeasure (averageLimit_nonneg T x m U)
  have hL (f : C(X, ℝ)) : (∫ y, f y ∂μ) = L (compactMap f) :=
    RealRMK.integral_rieszMeasure (averageLimit_nonneg T x m U) (compactMap f)
  have hpos : ∀ᶠ i in (U : Filter ℕ), 0 < m i :=
    hU (hm.eventually (eventually_gt_atTop 0))
  have hOne := (hL (ContinuousMap.const X 1)).trans (averageLimit_const T x m U hpos)
  have hmass : (μ univ).toReal = 1 := by
    simpa [ContinuousMap.const_apply, integral_const, measureReal_def] using hOne
  have hfin : μ univ ≠ ∞ := by
    intro h
    simp [h] at hmass
  haveI hμ : IsProbabilityMeasure μ :=
    ⟨(ENNReal.toReal_eq_toReal_iff' hfin ENNReal.one_ne_top).1 (by simpa using hmass)⟩
  refine ⟨μ, hμ, ⟨hT.measurable, ?_⟩, fun f => ?_⟩
  · apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map hT.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable]
    change (∫ y, (f.toContinuousMap.comp ⟨T, hT⟩) y ∂μ) = ∫ y, f.toContinuousMap y ∂μ
    rw [hL, hL]
    exact averageLimit_comp T hT x m hm U hU f.toContinuousMap
  · rw [hL]
    exact tendsto_averageLimit T x m U (compactMap f)

end Thesis.OrbitAverages
