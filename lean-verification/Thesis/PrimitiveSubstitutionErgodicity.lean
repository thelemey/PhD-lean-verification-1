import Thesis.PrimitiveFactorCenters

open MeasureTheory

namespace Thesis.ThueMorse

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] [Fintype A]

/-- The constant-length uniqueness assertion of Michel's theorem used in
thm:dynWb (5), for the one-sided orbit closure of a primitive fixed word. -/
theorem primitive_constantLength_unique_measure {b : Nat} (hb : 1 < b)
    (σ : A → Fin b → A) (w : Nat → A)
    (hprim : PrimitiveSubstitution (Nat.zero_lt_one.trans hb) σ)
    (hw : SubstitutionFixedWord σ w) :
    ∃! μ : ProbabilityMeasure (Nat → A), IsInvariantWordMeasure w μ :=
  unique_invariantWordMeasure_of_frequencyCenters w
    (primitive_factor_frequency_centers hb σ w hprim hw)

/-- Both ingredients cited in the strict-ergodicity step are available
for one-sided primitive constant-length substitutions. -/
theorem michel_constantLength : MichelConstantLength A where
  unique_measure := primitive_constantLength_unique_measure
  uniform_frequency := uniformFactorFrequencies_of_strictlyErgodic

/-- The strict-ergodicity and uniform-factor-frequency assertion of
thm:dynWb (5), applying Michel's uniqueness assertion to the primitive
digit substitution and its fixed word. -/
theorem finiteWord_strictlyErgodic {b N : Nat} [TopologicalSpace (Fin N)]
    [DiscreteTopology (Fin N)] [MeasurableSpace (Fin N)] [BorelSpace (Fin N)]
    (hb : 1 < b) (hN : 0 < N) :
    StrictlyErgodic (finiteWord b N hN) ∧ UniformFactorFrequencies (finiteWord b N hN) :=
  finiteWord_strictlyErgodic_of_michel michel_constantLength hb hN

end Thesis.ThueMorse
