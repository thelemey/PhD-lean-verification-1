import Thesis.SturmianDiophantine
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension

open Set MeasureTheory Filter

namespace Thesis.SturmianDensity

/-- Badly approximable slopes in the interval in `cor:palSturm`. -/
def badlyApproximableSlopes : Set ℝ := {a | a ∈ (Ioo (0 : ℝ) 1) ∧ BadlyApproximable a}

/-- The irrational slopes of characteristic Sturmian words with density
strictly larger than 1/2, expressed by the cited Fischler formula. -/
def exceptionalSlopes : Set ℝ :=
  {a | a ∈ Ioo (0 : ℝ) 1 ∧ ∃ ha : Irrational a,
    1 / 2 < (slopeFractions a ha).fischlerDensity}

private theorem badly_approximable_irrational {a : ℝ} (ha : BadlyApproximable a) :
    Irrational a := by
  intro ha'
  obtain ⟨r, rfl⟩ := ha'
  obtain ⟨c, hc, h⟩ := ha
  have hden : 0 < r.den := Nat.pos_of_ne_zero r.den_nz
  have hbad := h r.num r.den hden
  rw [Rat.cast_def, sub_self, abs_zero] at hbad
  have hpos : 0 < c / (r.den : ℝ) ^ 2 := by positivity
  exact (not_le_of_gt hpos) hbad

/-- The set equality in `cor:palSturm` (3), using the classical
criterion relating bounded quotients to bad approximability. -/
theorem exceptional_slopes_eq_badly_approximable :
    exceptionalSlopes = badlyApproximableSlopes := by
  ext a
  constructor
  · rintro ⟨ha, hi, hd⟩
    exact ⟨ha, (slope_density_gt_half_iff hi).mp hd⟩
  · rintro ⟨ha, hb⟩
    have hi := badly_approximable_irrational hb
    exact ⟨ha, hi, (slope_density_gt_half_iff hi).mpr hb⟩

/-- The null-set and Hausdorff-dimension assertions in `cor:palSturm` (3).
The classical metric facts used in the source are explicit premises. -/
theorem exceptional_slopes_measure_and_dimension
    (hKhinchin : volume badlyApproximableSlopes = 0)
    (hJarnik : dimH badlyApproximableSlopes = 1) :
    volume exceptionalSlopes = 0 ∧ dimH exceptionalSlopes = 1 := by
  rw [exceptional_slopes_eq_badly_approximable]
  exact ⟨hKhinchin, hJarnik⟩

/-- The almost-everywhere statement in `cor:palSturm` (2), using
Khinchin's quoted null-set result for bounded partial quotients. -/
theorem density_ae_eq_half
    (hKhinchin : volume {a | a ∈ Ioo (0 : ℝ) 1 ∧
      ∃ ha : Irrational a, (slopeFractions a ha).BoundedQuotients} = 0) :
    ∀ᵐ a ∂volume.restrict (Ioo (0 : ℝ) 1),
      ∃ ha : Irrational a, (slopeFractions a ha).fischlerDensity = 1 / 2 := by
  have hirr : ∀ᵐ a ∂(volume : Measure ℝ), Irrational a := by
    apply ae_iff.2
    have hrat := (countable_range (fun r : ℚ => (r : ℝ))).measure_zero (volume : Measure ℝ)
    simpa only [Irrational, not_not] using hrat
  have hnot : ∀ᵐ a ∂(volume : Measure ℝ),
      ¬ (a ∈ Ioo (0 : ℝ) 1 ∧ ∃ ha : Irrational a, (slopeFractions a ha).BoundedQuotients) := by
    apply ae_iff.2
    simpa only [not_not] using hKhinchin
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [hirr, hnot] with a hi hn ha
  exact ⟨hi, (density_eq_half_iff (slopeFractions a hi)).2 (fun hb => hn ⟨ha, hi, hb⟩)⟩

end Thesis.SturmianDensity
