import Thesis.ThueMorseSubstitution
import Thesis.WordOrbitClosure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace Thesis.ThueMorse

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]

/-- An invariant probability measure supported on the orbit closure. -/
def IsInvariantWordMeasure [MeasurableSpace A] (w : Nat → A)
    (μ : ProbabilityMeasure (Nat → A)) : Prop :=
  (μ : Measure (Nat → A)) (wordOrbitClosure w) = 1 ∧
    MeasurePreserving (fun x : Nat → A => shiftBy x 1) (μ : Measure (Nat → A)) μ

/-- Strict ergodicity combines minimality with uniqueness of the
invariant probability measure. -/
def StrictlyErgodic [MeasurableSpace A] (w : Nat → A) : Prop :=
  (∀ x ∈ wordOrbitClosure w, wordOrbitClosure x = wordOrbitClosure w) ∧
    ∃! μ : ProbabilityMeasure (Nat → A), IsInvariantWordMeasure w μ

noncomputable def factorFrequency (x : Nat → A) {k : Nat}
    (u : Fin k → A) (i n : Nat) : ℝ := by
  classical
  exact ((Finset.range n).filter (fun d => window x k (i + d) = u)).card / (n : ℝ)

/-- The frequency of each factor converges uniformly over all starting
positions and over the points in the subshift. -/
def UniformFactorFrequencies (w : Nat → A) : Prop :=
  ∀ k (u : Fin k → A), ∃ ρ : ℝ,
    ∀ ε > 0, ∃ M : Nat, ∀ n ≥ M, ∀ x ∈ wordOrbitClosure w, ∀ i,
      |factorFrequency x u i n - ρ| < ε

/-- The two cited implications in thm:dynWb (5): Michel's theorem on
primitive substitutions and the uniform-frequency consequence of unique
ergodicity, in their constant-length one-sided form. -/
structure MichelConstantLength (A : Type*) [Fintype A] [TopologicalSpace A]
    [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] : Prop where
  unique_measure : ∀ {b : Nat} (hb : 1 < b) (σ : A → Fin b → A) (w : Nat → A),
    PrimitiveSubstitution (Nat.zero_lt_one.trans hb) σ →
    SubstitutionFixedWord σ w →
    ∃! μ : ProbabilityMeasure (Nat → A), IsInvariantWordMeasure w μ
  uniform_frequency : ∀ w : Nat → A, StrictlyErgodic w → UniformFactorFrequencies w

/-- The conclusion of thm:dynWb (5), from the cited theorem of Michel
and the cited implication for uniform frequencies. Primitivity,
the fixed-point identity and minimality are checked without additional
mathematical premises. -/
theorem finiteWord_strictlyErgodic_of_michel {b N : Nat} [TopologicalSpace (Fin N)]
    [DiscreteTopology (Fin N)] [MeasurableSpace (Fin N)] [BorelSpace (Fin N)]
    (michel : MichelConstantLength (Fin N)) (hb : 1 < b) (hN : 0 < N) :
    StrictlyErgodic (finiteWord b N hN) ∧ UniformFactorFrequencies (finiteWord b N hN) := by
  have h : StrictlyErgodic (finiteWord b N hN) :=
    ⟨fun x hx => finiteWord_orbitClosure_minimal hb hN x hx,
      michel.unique_measure hb _ _ (digitSubstitution_primitive hb hN)
        (digitSubstitution_fixedWord hb hN)⟩
  exact ⟨h, michel.uniform_frequency _ h⟩

end Thesis.ThueMorse
