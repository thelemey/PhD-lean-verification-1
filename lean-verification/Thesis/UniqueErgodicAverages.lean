import Thesis.OrbitAverageLimits

open Filter MeasureTheory
open scoped Topology

namespace Thesis.OrbitAverages

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] [HasOuterApproxClosed X]

/-- Unique invariance gives uniform convergence of the orbit averages
of every continuous observable, including along arbitrary starting points. -/
theorem uniform_birkhoff_of_unique (T : X → X) (hT : Continuous T) (μ : Measure X)
    (hunique : ∀ ν : Measure X, IsProbabilityMeasure ν → MeasurePreserving T ν ν → ν = μ)
    (f : C(X, ℝ)) :
    ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, ∀ x,
      |birkhoffAverage ℝ T f n x - ∫ y, f y ∂μ| < ε := by
  intro ε hε
  by_contra! h
  choose m hm x hx using h
  have hm' : Tendsto m atTop atTop := tendsto_atTop.2 fun j =>
    (eventually_ge_atTop j).mono fun i hi => hi.trans (hm i)
  obtain ⟨U, hU⟩ := exists_ultrafilter_le (f := (atTop : Filter ℕ))
  obtain ⟨ν, hν, hinv, hlim⟩ := invariant_limit_of_orbit_averages T hT x m hm' U hU
  rw [hunique ν hν hinv] at hlim
  have hnear := Metric.tendsto_nhds.mp (hlim f) ε hε
  have hnear' : ∀ᶠ i in (U : Filter ℕ),
      |birkhoffAverage ℝ T f (m i) (x i) - ∫ y, f y ∂μ| < ε := by
    simpa only [Real.dist_eq] using hnear
  obtain ⟨i, hi⟩ := hnear'.exists
  exact (not_lt_of_ge (hx i)) hi

end Thesis.OrbitAverages
