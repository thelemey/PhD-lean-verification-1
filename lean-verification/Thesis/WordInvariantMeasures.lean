import Thesis.ThueMorseErgodicity
import Thesis.OrbitAverageLimits
import Mathlib.Topology.Metrizable.Urysohn

open Filter Set MeasureTheory
open scoped Topology

namespace Thesis.ThueMorse

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] [Fintype A]

/-- The closed subshift regarded as a space in its own right. -/
abbrev WordSubshift (w : Nat → A) := ↥(wordOrbitClosure w)

instance (w : Nat → A) : CompactSpace (WordSubshift w) := by
  letI : CompactSpace A := ⟨(Set.toFinite _).isCompact⟩
  exact isCompact_iff_compactSpace.1 isClosed_closure.isCompact

omit [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Fintype A] in
theorem word_mem_orbitClosure (w : Nat → A) : w ∈ wordOrbitClosure w := by
  apply subset_closure
  exact ⟨0, by funext j; simp [shiftBy]⟩

/-- Shift as a self-map of the subshift. -/
def subshiftShift (w : Nat → A) (x : WordSubshift w) : WordSubshift w :=
  ⟨shiftBy x.1 1, wordOrbitClosure_shift_mem x.2⟩

omit [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Fintype A] in
theorem continuous_shiftBy (n : Nat) : Continuous (fun x : Nat → A => shiftBy x n) :=
  continuous_pi fun j => continuous_apply (n + j)

omit [MeasurableSpace A] [BorelSpace A] [Fintype A] in
theorem continuous_subshiftShift (w : Nat → A) : Continuous (subshiftShift w) :=
  ((continuous_shiftBy 1).comp continuous_subtype_val).subtype_mk _

omit [MeasurableSpace A] [BorelSpace A] [Fintype A] in
theorem subshiftShift_iterate (w : Nat → A) (j : Nat) (x : WordSubshift w) :
    (((subshiftShift w)^[j]) x).val = shiftBy x.val j := by
  induction j with
  | zero => funext t; simp [shiftBy]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change shiftBy ((((subshiftShift w)^[j]) x).val) 1 = _
    rw [ih]
    funext t
    simp [shiftBy, Nat.add_assoc]

private theorem exists_subshift_measure (w : Nat → A) :
    ∃ μ : Measure (WordSubshift w), IsProbabilityMeasure μ ∧
      MeasurePreserving (subshiftShift w) μ μ := by
  obtain ⟨U, hU⟩ := exists_ultrafilter_le (f := (atTop : Filter ℕ))
  obtain ⟨μ, hμ, hpres, _⟩ := OrbitAverages.invariant_limit_of_orbit_averages
    (subshiftShift w) (continuous_subshiftShift w)
    (fun _ => ⟨w, word_mem_orbitClosure w⟩) id tendsto_id U hU
  exact ⟨μ, hμ, hpres⟩

/-- Push a probability measure on the subshift into the ambient word space. -/
noncomputable def ambientWordMeasure (w : Nat → A) (μ : Measure (WordSubshift w))
    [IsProbabilityMeasure μ] : ProbabilityMeasure (Nat → A) :=
  ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure (WordSubshift w))
    (f := (Subtype.val : WordSubshift w → Nat → A)) continuous_subtype_val.measurable.aemeasurable

theorem ambientWordMeasure_invariant (w : Nat → A) (μ : Measure (WordSubshift w))
    [IsProbabilityMeasure μ] (h : MeasurePreserving (subshiftShift w) μ μ) :
    IsInvariantWordMeasure w (ambientWordMeasure w μ) := by
  have hc : Measurable (Subtype.val : WordSubshift w → Nat → A) := continuous_subtype_val.measurable
  have hs := (continuous_shiftBy (A := A) 1).measurable
  change Measure.map Subtype.val μ (wordOrbitClosure w) = 1 ∧
    MeasurePreserving (fun x : Nat → A => shiftBy x 1) (Measure.map Subtype.val μ)
      (Measure.map Subtype.val μ)
  constructor
  · rw [Measure.map_apply hc (show MeasurableSet (wordOrbitClosure w) from
      isClosed_closure.measurableSet)]
    rw [show Subtype.val ⁻¹' wordOrbitClosure w = (univ : Set (WordSubshift w)) by simp]
    exact measure_univ
  · refine ⟨hs, ?_⟩
    rw [Measure.map_map hs hc]
    change Measure.map (Subtype.val ∘ subshiftShift w) μ = Measure.map Subtype.val μ
    rw [← Measure.map_map hc h.measurable, h.map_eq]

/-- The one-sided shift always admits an invariant probability on its
orbit closure. This assertion does not require primitivity. -/
theorem exists_invariantWordMeasure (w : Nat → A) :
    ∃ μ : ProbabilityMeasure (Nat → A), IsInvariantWordMeasure w μ := by
  obtain ⟨μ, hμ, hinv⟩ := exists_subshift_measure w
  letI := hμ
  exact ⟨ambientWordMeasure w μ, ambientWordMeasure_invariant w μ hinv⟩

/-- Uniqueness in the ambient formulation gives uniqueness for measures
on the subshift itself. -/
theorem exists_unique_subshift_measure (w : Nat → A)
    (h : ∃! μ : ProbabilityMeasure (Nat → A), IsInvariantWordMeasure w μ) :
    ∃ μ : Measure (WordSubshift w), IsProbabilityMeasure μ ∧
      MeasurePreserving (subshiftShift w) μ μ ∧
      ∀ ν : Measure (WordSubshift w), IsProbabilityMeasure ν →
        MeasurePreserving (subshiftShift w) ν ν → ν = μ := by
  obtain ⟨μ, hμ, hinv⟩ := exists_subshift_measure w
  obtain ⟨ρ, _, huniq⟩ := h
  letI := hμ
  refine ⟨μ, hμ, hinv, fun ν hν hv => ?_⟩
  letI := hν
  have he := (huniq _ (ambientWordMeasure_invariant w ν hv)).trans
    (huniq _ (ambientWordMeasure_invariant w μ hinv)).symm
  have hm : Measure.map (Subtype.val : WordSubshift w → Nat → A) ν =
      Measure.map Subtype.val μ := congrArg ProbabilityMeasure.toMeasure he
  have hc := MeasurableEmbedding.subtype_coe (s := wordOrbitClosure w)
    (isClosed_closure.measurableSet)
  ext s hs
  have hEq := congrArg (fun η : Measure (Nat → A) => η (Subtype.val '' s)) hm
  simpa only [hc.map_apply, Set.preimage_image_eq _ Subtype.val_injective] using hEq

end Thesis.ThueMorse
