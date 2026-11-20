import Thesis.WordUniformFrequencies
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.MeasurableSpace.Pi

open Set MeasureTheory Filter
open scoped BigOperators

namespace Thesis.ThueMorse

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] [Fintype A]

private def prefixSets (A : Type*) : Set (Set (Nat → A)) :=
  {s | ∃ (k : Nat) (B : Set (Fin k → A)), s = (fun x => window x k 0) ⁻¹' B}

omit [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Fintype A] in
private theorem isPiSystem_prefixSets : IsPiSystem (prefixSets A) := by
  rintro s ⟨k, B, rfl⟩ t ⟨l, C, rfl⟩ _
  let m := max k l
  let pk : (Fin m → A) → (Fin k → A) := fun g j => g (Fin.castLE (le_max_left k l) j)
  let pl : (Fin m → A) → (Fin l → A) := fun g j => g (Fin.castLE (le_max_right k l) j)
  refine ⟨m, pk ⁻¹' B ∩ pl ⁻¹' C, ?_⟩
  ext x
  change (window x k 0 ∈ B ∧ window x l 0 ∈ C) ↔
    pk (window x m 0) ∈ B ∧ pl (window x m 0) ∈ C
  rfl

private theorem measurableSpace_eq_generateFrom_prefixSets :
    (inferInstance : MeasurableSpace (Nat → A)) = MeasurableSpace.generateFrom (prefixSets A) := by
  apply le_antisymm
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_mono
    rintro s ⟨i, B, _, rfl⟩
    refine ⟨i + 1, (fun f : Fin (i + 1) → A => f (Fin.last i)) ⁻¹' B, ?_⟩
    ext x
    simp [Function.eval, window]
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨k, B, rfl⟩
    exact (isOpen_discrete (s := B)).measurableSet.preimage (continuous_window k 0).measurable

/-- Finite probability measures on words are determined by their
values on single-prefix cylinders. -/
theorem probabilityMeasure_ext_prefixCylinder (μ ν : ProbabilityMeasure (Nat → A))
    (h : ∀ k (u : Fin k → A), (μ : Measure (Nat → A)) (prefixCylinder u) =
      (ν : Measure (Nat → A)) (prefixCylinder u)) : μ = ν := by
  apply Subtype.ext
  letI : IsProbabilityMeasure (μ : Measure (Nat → A)) := μ.2
  letI : IsProbabilityMeasure (ν : Measure (Nat → A)) := ν.2
  refine ext_of_generate_finite (μ := (μ : Measure (Nat → A))) (ν := (ν : Measure (Nat → A)))
    (prefixSets A) measurableSpace_eq_generateFrom_prefixSets isPiSystem_prefixSets ?_ (by simp)
  rintro s ⟨k, B, rfl⟩
  let f := fun x : Nat → A => window x k 0
  have hf : Measurable f := (continuous_window k 0).measurable
  have hB : MeasurableSet B := (isOpen_discrete (s := B)).measurableSet
  have hmap : Measure.map f (μ : Measure (Nat → A)) = Measure.map f (ν : Measure (Nat → A)) := by
    apply Measure.ext_of_singleton
    intro u
    rw [Measure.map_apply hf (measurableSet_singleton u), Measure.map_apply hf (measurableSet_singleton u)]
    exact h k u
  rw [← Measure.map_apply hf hB, ← Measure.map_apply hf hB, hmap]

private noncomputable def frequencyIndicator {k : Nat} (u : Fin k → A) (d : Nat) : (Nat → A) → ℝ :=
  ((fun x : Nat → A => shiftBy x d) ⁻¹' prefixCylinder u).indicator (1 : (Nat → A) → ℝ)

omit [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Fintype A] in
private theorem factorFrequency_eq_indicatorSum {k : Nat} (u : Fin k → A) (n : Nat) :
    (fun x : Nat → A => factorFrequency x u 0 n) =
      fun x => (n : ℝ)⁻¹ * (∑ d ∈ Finset.range n, frequencyIndicator u d) x := by
  classical
  funext x
  rw [factorFrequency, Finset.natCast_card_filter, div_eq_mul_inv, mul_comm]
  simp only [Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [frequencyIndicator, Set.indicator_apply, Set.mem_preimage, prefixCylinder,
    Set.mem_setOf_eq, Pi.one_apply, Nat.zero_add]
  rw [show window (shiftBy x d) k 0 = window x k d by funext j; simp [window, shiftBy]]

private theorem frequencyIndicator_integrable {k : Nat} (u : Fin k → A) (d : Nat)
    (μ : ProbabilityMeasure (Nat → A)) :
    Integrable (frequencyIndicator u d) (μ : Measure (Nat → A)) :=
  (integrable_const 1).indicator
    ((isClopen_prefixCylinder u).1.measurableSet.preimage (continuous_shiftBy d).measurable)

private theorem factorFrequency_integrable {k : Nat} (u : Fin k → A) (n : Nat)
    (μ : ProbabilityMeasure (Nat → A)) :
    Integrable (fun x => factorFrequency x u 0 n) (μ : Measure (Nat → A)) := by
  rw [factorFrequency_eq_indicatorSum]
  simpa only [Finset.sum_apply] using
    (integrable_finset_sum (Finset.range n) fun d _ => frequencyIndicator_integrable u d μ).const_mul
      ((n : ℝ)⁻¹)

private theorem integral_factorFrequency_eq {w : Nat → A} {μ : ProbabilityMeasure (Nat → A)}
    (hμ : IsInvariantWordMeasure w μ) {k n : Nat} (hn : 0 < n) (u : Fin k → A) :
    (∫ x, factorFrequency x u 0 n ∂(μ : Measure (Nat → A))) =
      (μ : Measure (Nat → A)).real (prefixCylinder u) := by
  have hC := (isClopen_prefixCylinder u).1.measurableSet
  have hTerm (d : Nat) :
      (∫ x, frequencyIndicator u d x ∂(μ : Measure (Nat → A))) =
        (μ : Measure (Nat → A)).real (prefixCylinder u) := by
    rw [frequencyIndicator, integral_indicator_one (hC.preimage (continuous_shiftBy d).measurable)]
    have hp := hμ.2.iterate d
    have he : (fun x : Nat → A => shiftBy x 1)^[d] = fun x => shiftBy x d :=
      funext fun x => shift_iterate x d
    rw [he] at hp
    exact hp.measureReal_preimage hC.nullMeasurableSet
  rw [factorFrequency_eq_indicatorSum, integral_const_mul]
  simp only [Finset.sum_apply]
  rw [integral_finset_sum]
  · simp only [hTerm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_mul]
  · exact fun d _ => frequencyIndicator_integrable u d μ

private theorem cylinder_mass_close {w : Nat → A} {μ : ProbabilityMeasure (Nat → A)}
    (hμ : IsInvariantWordMeasure w μ) {k n : Nat} (hn : 0 < n) (u : Fin k → A)
    {ρ ε : ℝ} (h : ∀ x ∈ wordOrbitClosure w, |factorFrequency x u 0 n - ρ| ≤ ε) :
    |(μ : Measure (Nat → A)).real (prefixCylinder u) - ρ| ≤ ε := by
  have hs : ∀ᵐ x ∂(μ : Measure (Nat → A)), x ∈ wordOrbitClosure w :=
    (mem_ae_iff_prob_eq_one (show MeasurableSet (wordOrbitClosure w) from
      isClosed_closure.measurableSet)).2 hμ.1
  have hi := factorFrequency_integrable u n μ
  have hm := integral_factorFrequency_eq hμ hn u
  have hl : ∀ᵐ x ∂(μ : Measure (Nat → A)), ρ - ε ≤ factorFrequency x u 0 n :=
    hs.mono fun x hx => by have := (abs_le.mp (h x hx)).1; linarith
  have hr : ∀ᵐ x ∂(μ : Measure (Nat → A)), factorFrequency x u 0 n ≤ ρ + ε :=
    hs.mono fun x hx => by have := (abs_le.mp (h x hx)).2; linarith
  have h₁ := integral_mono_ae (integrable_const _) hi hl
  have h₂ := integral_mono_ae hi (integrable_const _) hr
  rw [hm, integral_const] at h₁ h₂
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at h₁ h₂
  simp only [measureReal_def]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Arbitrarily accurate common approximations for finite-window
frequencies determine the supported invariant probability uniquely. -/
theorem unique_invariantWordMeasure_of_frequencyCenters (w : Nat → A)
    (h : ∀ k (u : Fin k → A) ε, 0 < ε → ∃ n : Nat, 0 < n ∧ ∃ ρ : ℝ,
      ∀ x ∈ wordOrbitClosure w, |factorFrequency x u 0 n - ρ| ≤ ε) :
    ∃! μ : ProbabilityMeasure (Nat → A), IsInvariantWordMeasure w μ := by
  obtain ⟨μ, hμ⟩ := exists_invariantWordMeasure w
  refine ⟨μ, hμ, fun ν hν => probabilityMeasure_ext_prefixCylinder ν μ ?_⟩
  intro k u
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
  change (ν : Measure (Nat → A)).real (prefixCylinder u) =
    (μ : Measure (Nat → A)).real (prefixCylinder u)
  let v := (ν : Measure (Nat → A)).real (prefixCylinder u)
  let z := (μ : Measure (Nat → A)).real (prefixCylinder u)
  by_contra hne
  have hd : 0 < |v - z| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn, ρ, hfreq⟩ := h k u (|v - z| / 3) (by positivity)
  have h₁ := cylinder_mass_close hν hn u hfreq
  have h₂ := cylinder_mass_close hμ hn u hfreq
  change |v - ρ| ≤ |v - z| / 3 at h₁
  change |z - ρ| ≤ |v - z| / 3 at h₂
  have htri : |v - z| ≤ |v - ρ| + |z - ρ| := by
    rw [abs_sub_comm z ρ]
    exact abs_sub_le v ρ z
  linarith

/-- Uniform factor frequencies give a unique invariant probability,
the reverse implication of the equivalence cited in thm:dynWb. -/
theorem unique_invariantWordMeasure_of_uniformFactorFrequencies (w : Nat → A)
    (h : UniformFactorFrequencies w) :
    ∃! μ : ProbabilityMeasure (Nat → A), IsInvariantWordMeasure w μ := by
  apply unique_invariantWordMeasure_of_frequencyCenters w
  intro k u ε hε
  obtain ⟨ρ, hρ⟩ := h k u
  obtain ⟨M, hM⟩ := hρ ε hε
  exact ⟨M + 1, Nat.succ_pos _, ρ, fun x hx => (hM (M + 1) (Nat.le_succ _) x hx 0).le⟩

theorem unique_invariantWordMeasure_iff_uniformFactorFrequencies (w : Nat → A) :
    (∃! μ : ProbabilityMeasure (Nat → A), IsInvariantWordMeasure w μ) ↔ UniformFactorFrequencies w :=
  ⟨uniformFactorFrequencies_of_unique w, unique_invariantWordMeasure_of_uniformFactorFrequencies w⟩

end Thesis.ThueMorse
