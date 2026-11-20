import Thesis.FactorialCorrelations
import Thesis.VanDerCorputLimit
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter Topology Set MeasureTheory
open scoped BigOperators ENNReal

namespace Thesis.FactorialWord

open Thesis.VanDerCorput

private abbrev UnitCircle := AddCircle (1 : ℝ)

private local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private noncomputable def circleUniform : ProbabilityMeasure UnitCircle :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

private noncomputable def circleEmpirical (x : Nat → ℝ) (N : Nat) :
    ProbabilityMeasure UnitCircle := by
  let μ : Measure UnitCircle :=
    ((N + 1 : Nat) : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range (N + 1), Measure.dirac (x n : UnitCircle)
  have hN : ((N + 1 : Nat) : ℝ≥0∞) ≠ 0 := by simp
  refine ⟨μ, ⟨?_⟩⟩
  simp only [μ, Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_range, nsmul_one]
  exact ENNReal.inv_mul_cancel hN (ENNReal.natCast_ne_top _)

private theorem integral_circleEmpirical (x : Nat → ℝ) (N : Nat) (f : C(UnitCircle, ℂ)) :
    (∫ y, f y ∂(circleEmpirical x N : Measure UnitCircle)) =
      mean (fun n => f (x n : UnitCircle)) (N + 1) := by
  change (∫ y, f y ∂((((N + 1 : Nat) : ℝ≥0∞)⁻¹ •
    ∑ n ∈ Finset.range (N + 1), Measure.dirac (x n : UnitCircle)) : Measure UnitCircle)) = _
  rw [integral_smul_measure, integral_finset_sum_measure]
  · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simp [mean]
  · exact fun _ _ => integrable_dirac

private theorem integral_circleUniform (h : Int) :
    (∫ y, fourier h y ∂(circleUniform : Measure UnitCircle)) = if h = 0 then 1 else 0 := by
  by_cases hh : h = 0
  · subst h
    simp [fourier_zero]
  · rw [if_neg hh]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hh zero_lt_one)

private theorem fourier_frequency (h : Int) (x : ℝ) :
    fourier h (x : UnitCircle) = oscillation (2 * Real.pi * (h : ℝ) * x) := by
  rw [fourier_coe_apply, oscillation]
  push_cast
  congr 1
  ring

private theorem integrals_lipschitz (μ : ProbabilityMeasure UnitCircle) (f g : C(UnitCircle, ℂ)) :
    ‖(∫ y, f y ∂(μ : Measure UnitCircle)) - ∫ y, g y ∂(μ : Measure UnitCircle)‖ ≤
      ‖f - g‖ := by
  rw [← integral_sub (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
    (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))]
  simpa only [measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const
      (Eventually.of_forall (f - g).norm_coe_le_norm :
        ∀ᵐ y ∂(μ : Measure UnitCircle), ‖(f - g) y‖ ≤ ‖f - g‖)

private theorem circleEmpirical_tendsto (x : Nat → ℝ)
    (h : ∀ h : ℤ, h ≠ 0 →
      Tendsto (mean (fun n => oscillation (2 * Real.pi * (h : ℝ) * x n))) atTop (𝓝 0)) :
    Tendsto (circleEmpirical x) atTop (𝓝 circleUniform) := by
  let moment (μ : ProbabilityMeasure UnitCircle) (f : C(UnitCircle, ℂ)) :=
    ∫ y, f y ∂(μ : Measure UnitCircle)
  let converges (f : C(UnitCircle, ℂ)) : Prop :=
    Tendsto (fun N => moment (circleEmpirical x N) f) atTop (𝓝 (moment circleUniform f))
  have hspan : ∀ f ∈ Submodule.span ℂ (Set.range (@fourier 1)), converges f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨n, rfl⟩ := hf
      change Tendsto (fun N => ∫ y, fourier n y ∂(circleEmpirical x N : Measure UnitCircle))
        atTop (𝓝 (∫ y, fourier n y ∂(circleUniform : Measure UnitCircle)))
      simp only [integral_circleEmpirical, integral_circleUniform]
      by_cases hn : n = 0
      · subst n
        have he (N : Nat) : mean (fun _ => (1 : ℂ)) (N + 1) = 1 := by
          simp only [mean, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
            Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
          exact inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero N)
        simp only [fourier_zero, if_pos rfl, he]
        exact tendsto_const_nhds
      · simpa only [fourier_frequency, if_neg hn] using (h n hn).comp (tendsto_add_atTop_nat 1)
    | zero => simp [converges, moment]
    | add f g _ _ hf hg =>
      dsimp [converges, moment] at *
      have hfI (μ : ProbabilityMeasure UnitCircle) := f.continuous.integrable_of_hasCompactSupport
        (μ := (μ : Measure UnitCircle)) (HasCompactSupport.of_compactSpace f)
      have hgI (μ : ProbabilityMeasure UnitCircle) := g.continuous.integrable_of_hasCompactSupport
        (μ := (μ : Measure UnitCircle)) (HasCompactSupport.of_compactSpace g)
      simpa only [ContinuousMap.add_apply, integral_add (hfI _) (hgI _)] using hf.add hg
    | smul c f _ hf =>
      dsimp [converges, moment] at *
      simpa only [ContinuousMap.smul_apply, integral_const_mul, smul_eq_mul] using hf.const_smul c
  have hdense : Dense (Submodule.span ℂ (Set.range (@fourier 1)) : Set C(UnitCircle, ℂ)) := by
    rw [dense_iff_closure_eq]
    exact congrArg SetLike.coe (span_fourier_closure_eq_top (T := 1))
  have hall (f : C(UnitCircle, ℂ)) : converges f := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨g, hg, hfg⟩ := hdense.exists_dist_lt f (show 0 < ε / 3 by positivity)
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hspan g hg) (ε / 3) (by positivity)
    refine ⟨N₀, fun N hN => ?_⟩
    have h1 := integrals_lipschitz (circleEmpirical x N) f g
    have h2 := integrals_lipschitz circleUniform g f
    rw [norm_sub_rev g f] at h2
    rw [dist_eq_norm] at hfg
    have htri := dist_triangle (moment (circleEmpirical x N) f)
      (moment (circleEmpirical x N) g) (moment circleUniform f)
    have htri' := dist_triangle (moment (circleEmpirical x N) g)
      (moment circleUniform g) (moment circleUniform f)
    have hmid := hN₀ N hN
    dsimp only [moment] at *
    rw [dist_eq_norm] at hmid
    simp only [dist_eq_norm] at htri htri' ⊢
    linarith
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).2
  intro f
  exact hall f.toContinuousMap

private def arc (a b : ℝ) : Set UnitCircle :=
  ((↑) : ℝ → UnitCircle) '' Ico a b

private theorem mem_arc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (x : ℝ) :
    (x : UnitCircle) ∈ arc a b ↔ Int.fract x ∈ Ico a b := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hf : Int.fract y = y := Int.fract_eq_self.mpr ⟨ha.trans hy.1, hy.2.trans_le hb⟩
    have he := congrArg (fun z : UnitCircle => (AddCircle.equivIco 1 0 z : ℝ)) hyx
    simp only [AddCircle.coe_equivIco_mk_apply, div_one, mul_one, hf] at he
    rwa [← he]
  · intro hx
    exact ⟨Int.fract x, hx, AddCircle.coe_fract x⟩

private theorem measurableSet_arc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    MeasurableSet (arc a b) := by
  have he : arc a b =
      (fun z : UnitCircle => (AddCircle.measurableEquivIco 1 0 z : ℝ)) ⁻¹' Ico a b := by
    ext z
    induction z using QuotientAddGroup.induction_on with
    | _ x =>
      rw [mem_arc ha hb]
      change _ ↔ (AddCircle.equivIco 1 0 (x : UnitCircle) : ℝ) ∈ Ico a b
      simp only [AddCircle.coe_equivIco_mk_apply, div_one, mul_one]
  rw [he]
  exact measurableSet_Ico.preimage
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable)

private theorem volume_unit_circle :
    (volume : Measure UnitCircle) = (circleUniform : Measure UnitCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp [circleUniform]

private theorem circleUniform_arc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (circleUniform : Measure UnitCircle) (arc a b) = ENNReal.ofReal (b - a) := by
  rw [← volume_unit_circle, AddCircle.add_projection_respects_measure 1 0 (measurableSet_arc ha hb),
    zero_add]
  have he : (((↑) : ℝ → UnitCircle) ⁻¹' arc a b) ∩ Ico 0 1 = Ico a b := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_arc ha hb]
    constructor
    · rintro ⟨hy, hunit⟩
      rwa [Int.fract_eq_self.mpr hunit] at hy
    · intro hy
      have hy' : y ∈ Ico 0 1 := ⟨ha.trans hy.1, hy.2.trans_le hb⟩
      exact ⟨(Int.fract_eq_self.mpr hy').symm ▸ hy, hy'⟩
  have heq := (EventuallyEq.rfl :
    (((↑) : ℝ → UnitCircle) ⁻¹' arc a b) =ᵐ[(volume : Measure ℝ)]
      (((↑) : ℝ → UnitCircle) ⁻¹' arc a b)).inter
    (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := 0) (b := 1))
  rw [← measure_congr heq]
  change volume ((((↑) : ℝ → UnitCircle) ⁻¹' arc a b) ∩ Ico 0 1) = _
  rw [he, Real.volume_Ico]

private theorem circleUniform_arc_frontier (a b : ℝ) :
    (circleUniform : Measure UnitCircle) (frontier (arc a b)) = 0 := by
  let q : ℝ → UnitCircle := (↑)
  have hclosed : IsClosed (q '' Icc a b) :=
    (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hopen : IsOpen (q '' Ioo a b) := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hclose : closure (arc a b) ⊆ q '' Icc a b :=
    closure_minimal (image_subset _ Ico_subset_Icc_self) hclosed
  have hint : q '' Ioo a b ⊆ interior (arc a b) :=
    interior_maximal (image_subset _ Ioo_subset_Ico_self) hopen
  have hsub : frontier (arc a b) ⊆ {q a, q b} := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hclose hz.1
    have he : ¬ (a < y ∧ y < b) := fun h => hz.2 (hint ⟨y, h, rfl⟩)
    rcases lt_or_eq_of_le hy.1 with hal | rfl
    · have : y = b := le_antisymm hy.2 (le_of_not_gt fun hl => he ⟨hal, hl⟩)
      simp [this]
    · simp
  rw [← volume_unit_circle]
  exact measure_mono_null hsub (by
    change volume ({q a} ∪ {q b}) = 0
    have hs (z : UnitCircle) : volume ({z} : Set UnitCircle) = 0 := by
      have h := AddCircle.volume_closedBall (T := (1 : ℝ)) (x := z) 0
      simpa only [Metric.closedBall_zero, mul_zero, min_eq_right zero_le_one,
        ENNReal.ofReal_zero] using h
    exact measure_union_null (hs _) (hs _))

private theorem empirical_arc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (x : Nat → ℝ) (N : Nat) :
    ((circleEmpirical x N : Measure UnitCircle) (arc a b)).toReal =
      fractionalFrequency x a b (N + 1) := by
  classical
  change ((((N + 1 : Nat) : ℝ≥0∞)⁻¹ •
    ∑ n ∈ Finset.range (N + 1), Measure.dirac (x n : UnitCircle)) (arc a b)).toReal = _
  simp only [Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply, Measure.dirac_apply]
  have he (n : Nat) :
      (arc a b).indicator (1 : UnitCircle → ℝ≥0∞) (x n : UnitCircle) =
      if Int.fract (x n) ∈ Ico a b then 1 else 0 := by
    simp [Set.indicator, mem_arc ha hb]
  simp only [he, ← Finset.sum_filter, Finset.sum_const, nsmul_one, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, fractionalFrequency, div_eq_mul_inv, mul_comm]

/-- The direction of the classical Weyl criterion used in the thesis. -/
def WeylCriterion : Prop :=
  ∀ x : Nat → ℝ,
    (∀ h : ℤ, h ≠ 0 →
      Tendsto (mean (fun n => oscillation (2 * Real.pi * (h : ℝ) * x n))) atTop (𝓝 0)) →
    Equidistributed x

/-- The implication of the classical Weyl criterion cited in the dissertation.
Fourier monomials determine weak convergence on the circle by their uniform
density. The half-open arcs have null frontier for the uniform measure. -/
theorem weylCriterion : WeylCriterion := by
  intro x hx a b ha hab hb
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hweak := circleEmpirical_tendsto x hx
  have hc : Tendsto (fun N => (circleEmpirical x N : Measure UnitCircle) (arc a b))
      atTop (𝓝 ((circleUniform : Measure UnitCircle) (arc a b))) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak
      (circleUniform_arc_frontier a b)
  rw [circleUniform_arc ha hb] at hc
  have ht := (ENNReal.continuousAt_toReal ENNReal.ofReal_ne_top).tendsto.comp hc
  change Tendsto (fun N => ((circleEmpirical x N : Measure UnitCircle) (arc a b)).toReal)
    atTop (𝓝 (ENNReal.ofReal (b - a)).toReal) at ht
  simpa only [empirical_arc ha hb, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] using ht

end Thesis.FactorialWord
