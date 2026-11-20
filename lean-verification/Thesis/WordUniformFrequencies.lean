import Thesis.WordInvariantMeasures
import Thesis.UniqueErgodicAverages
import Mathlib.Topology.Algebra.Indicator

open Filter Set MeasureTheory
open scoped Topology BigOperators

namespace Thesis.ThueMorse

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] [Fintype A]

/-- The cylinder of words starting with a specified factor. -/
def prefixCylinder {k : Nat} (u : Fin k → A) : Set (Nat → A) :=
  {x | window x k 0 = u}

omit [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Fintype A] in
theorem continuous_window (k i : Nat) : Continuous (fun x : Nat → A => window x k i) :=
  continuous_pi fun j => continuous_apply (i + j.val)

theorem isClopen_prefixCylinder {k : Nat} (u : Fin k → A) :
    IsClopen (prefixCylinder u) :=
  (isClopen_discrete ({u} : Set (Fin k → A))).preimage (continuous_window k 0)

private noncomputable def prefixObservable (w : Nat → A) {k : Nat} (u : Fin k → A) :
    C(WordSubshift w, ℝ) :=
  ⟨(Subtype.val ⁻¹' prefixCylinder u).indicator (fun _ => 1),
    ((isClopen_prefixCylinder u).preimage continuous_subtype_val).continuous_indicator
      continuous_const⟩

private theorem frequency_eq_birkhoff (w : Nat → A) {k : Nat} (u : Fin k → A)
    (x : WordSubshift w) (i n : Nat) :
    factorFrequency x.val u i n =
      birkhoffAverage ℝ (subshiftShift w) (prefixObservable w u) n
        (((subshiftShift w)^[i]) x) := by
  classical
  unfold factorFrequency birkhoffAverage birkhoffSum
  rw [Finset.natCast_card_filter, div_eq_mul_inv, mul_comm]
  apply congrArg ((n : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro d _
  simp only [prefixObservable, ContinuousMap.coe_mk, Set.indicator_apply, Set.mem_preimage,
    subshiftShift_iterate, prefixCylinder, Set.mem_setOf_eq]
  have he : window (shiftBy (shiftBy x.val i) d) k 0 = window x.val k (i + d) := by
    funext j
    simp [shiftBy, window, Nat.add_assoc]
  rw [he]

/-- The uniform-frequency implication used in thm:dynWb (5).
It suffices to have exactly one invariant probability measure
supported on the one-sided orbit closure. -/
theorem uniformFactorFrequencies_of_unique (w : Nat → A)
    (h : ∃! μ : ProbabilityMeasure (Nat → A), IsInvariantWordMeasure w μ) :
    UniformFactorFrequencies w := by
  obtain ⟨μ, _, _, huniq⟩ := exists_unique_subshift_measure w h
  intro k u
  let f := prefixObservable w u
  refine ⟨∫ y, f y ∂μ, fun ε hε => ?_⟩
  obtain ⟨M, hM⟩ := OrbitAverages.uniform_birkhoff_of_unique (subshiftShift w)
    (continuous_subshiftShift w) μ huniq f ε hε
  refine ⟨M, fun n hn x hx i => ?_⟩
  rw [show factorFrequency x u i n = birkhoffAverage ℝ (subshiftShift w) f n
        (((subshiftShift w)^[i]) ⟨x, hx⟩) from frequency_eq_birkhoff w u ⟨x, hx⟩ i n]
  exact hM n hn _

theorem uniformFactorFrequencies_of_strictlyErgodic (w : Nat → A)
    (h : StrictlyErgodic w) : UniformFactorFrequencies w :=
  uniformFactorFrequencies_of_unique w h.2

/-- Apply Michel's uniqueness assertion to the primitive fixed point,
then derive uniform frequencies from that uniqueness. -/
theorem finiteWord_strictlyErgodic_of_michel_unique {b N : Nat} [TopologicalSpace (Fin N)]
    [DiscreteTopology (Fin N)] [MeasurableSpace (Fin N)] [BorelSpace (Fin N)]
    (hb : 1 < b) (hN : 0 < N)
    (michel : ∀ {b : Nat} (hb : 1 < b) (σ : Fin N → Fin b → Fin N) (w : Nat → Fin N),
      PrimitiveSubstitution (Nat.zero_lt_one.trans hb) σ → SubstitutionFixedWord σ w →
      ∃! μ : ProbabilityMeasure (Nat → Fin N), IsInvariantWordMeasure w μ) :
    StrictlyErgodic (finiteWord b N hN) ∧ UniformFactorFrequencies (finiteWord b N hN) := by
  have h : StrictlyErgodic (finiteWord b N hN) :=
    ⟨fun x hx => finiteWord_orbitClosure_minimal hb hN x hx,
      michel hb _ _ (digitSubstitution_primitive hb hN) (digitSubstitution_fixedWord hb hN)⟩
  exact ⟨h, uniformFactorFrequencies_of_strictlyErgodic _ h⟩

end Thesis.ThueMorse
