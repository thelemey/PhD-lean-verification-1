import Thesis.BadlyApproximableNull
import Thesis.SturmianWordDensityConsequences

open Set MeasureTheory Filter

namespace Thesis.SturmianDensity

/-- The exceptional slopes in cor:palSturm have Lebesgue measure zero. -/
theorem volume_wordExceptionalSlopes_zero : volume wordExceptionalSlopes = 0 := by
  rw [wordExceptionalSlopes_eq_badlyApproximable, volume_badlyApproximableSlopes_zero]

/-- Almost every slope in the unit interval gives palindrome density one half. -/
theorem characteristic_word_density_ae_eq_half_unconditional :
    ∀ᵐ a ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ p q : Nat, 0 < q →
      (BelowPalDensity (FactorTree.characteristicWord a) p q ↔ (p : ℝ) / q < 1 / 2) := by
  apply characteristic_word_density_ae_eq_half
  apply measure_mono_null _ volume_badlyApproximableSlopes_zero
  rintro a ⟨ha, hirr, hb⟩
  exact ⟨ha, (slopeFractions_bounded_iff_badlyApproximable hirr).1 hb⟩

end Thesis.SturmianDensity
