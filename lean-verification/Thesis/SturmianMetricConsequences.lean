import Thesis.BadlyApproximableDimension
import Thesis.SturmianNullConsequences

open MeasureTheory

namespace Thesis.SturmianDensity

/-- The source identifies the exceptional slopes by the dichotomy and
then applies the classical nullity and dimension results to that set. -/
theorem wordExceptionalSlopes_measure_and_dimension_unconditional :
    volume wordExceptionalSlopes = 0 ∧ dimH wordExceptionalSlopes = 1 :=
  wordExceptionalSlopes_measure_and_dimension volume_badlyApproximableSlopes_zero
    dimH_badlyApproximableSlopes_eq_one

end Thesis.SturmianDensity
