import Thesis.PalindromicDensityReal
import Thesis.SturmianMetricConsequences

open Set Filter MeasureTheory Topology

namespace Thesis.SturmianDensity

/-- Fischler's formula for the density of the characteristic word itself. -/
theorem characteristic_palindromicDensity {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) :
    palindromicDensity (FactorTree.characteristicWord a) = (slopeFractions a hirr).fischlerDensity :=
  palindromicDensity_eq_of_cut ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans
    (half_le_density (slopeFractions a hirr))) fun _ _ hq =>
      characteristic_below_density_iff ha ha' hirr hq

theorem characteristic_palindromicDensity_unbounded {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) (h : ¬ (slopeFractions a hirr).BoundedQuotients) :
    palindromicDensity (FactorTree.characteristicWord a) = 1 / 2 := by
  rw [characteristic_palindromicDensity ha ha' hirr, density_unbounded _ h]

theorem characteristic_palindromicDensity_bounded {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) (A : Nat) (h : ∀ k, partialQuotient a k ≤ A) :
    (A + 2 : ℝ) / (2 * A + 3) ≤ palindromicDensity (FactorTree.characteristicWord a) ∧
      (1 : ℝ) / 2 < (A + 2 : ℝ) / (2 * A + 3) := by
  rw [characteristic_palindromicDensity ha ha' hirr]
  exact density_bounded (slopeFractions a hirr) A h

theorem characteristic_palindromicDensity_gt_half_iff {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) :
    1 / 2 < palindromicDensity (FactorTree.characteristicWord a) ↔ BadlyApproximable a := by
  rw [characteristic_palindromicDensity ha ha' hirr]
  exact slope_density_gt_half_iff hirr

/-- The bounds and lower endpoint in cor:palSturm (1). -/
theorem characteristic_palindromicDensity_bounds {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) :
    1 / 2 ≤ palindromicDensity (FactorTree.characteristicWord a) ∧
      palindromicDensity (FactorTree.characteristicWord a) ≤ 1 / goldenRatio ∧
      (palindromicDensity (FactorTree.characteristicWord a) = 1 / 2 ↔
        ¬ (slopeFractions a hirr).BoundedQuotients) := by
  rw [characteristic_palindromicDensity ha ha' hirr]
  obtain ⟨hlo, hhi⟩ := density_bounds (slopeFractions a hirr)
  exact ⟨hlo, hhi, density_eq_half_iff _⟩

/-- The almost-everywhere equality in cor:palSturm (2). -/
theorem characteristic_palindromicDensity_ae_eq_half :
    ∀ᵐ a ∂volume.restrict (Ioo (0 : ℝ) 1),
      palindromicDensity (FactorTree.characteristicWord a) = 1 / 2 := by
  filter_upwards [characteristic_word_density_ae_eq_half_unconditional] with a h
  exact palindromicDensity_eq_of_cut (by norm_num) h

/-- The exceptional set in cor:palSturm (3), in terms of real density. -/
theorem characteristic_palindromicDensity_exceptional_eq :
    {a ∈ Ioo (0 : ℝ) 1 | Irrational a ∧
      1 / 2 < palindromicDensity (FactorTree.characteristicWord a)} = badlyApproximableSlopes := by
  rw [← wordExceptionalSlopes_eq_badlyApproximable]
  ext a
  have h := belowPalDensity_iff_lt_palindromicDensity (FactorTree.characteristicWord a)
    (p := 1) (q := 2) (by decide)
  simp only [wordExceptionalSlopes, mem_setOf_eq, Nat.cast_one, Nat.cast_ofNat] at h ⊢
  rw [h]

theorem characteristic_palindromicDensity_exceptional_measure_and_dimension :
    let E := {a ∈ Ioo (0 : ℝ) 1 | Irrational a ∧
      1 / 2 < palindromicDensity (FactorTree.characteristicWord a)}
    volume E = 0 ∧ dimH E = 1 := by
  dsimp only
  rw [characteristic_palindromicDensity_exceptional_eq, ← wordExceptionalSlopes_eq_badlyApproximable]
  exact wordExceptionalSlopes_measure_and_dimension_unconditional

/-- The maximal value and the next spectral bound in cor:palSturm (4). -/
theorem characteristic_palindromicDensity_spectrum {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) :
    (palindromicDensity (FactorTree.characteristicWord a) = 1 / goldenRatio ↔
      ∃ N, ∀ k ≥ N, partialQuotient a k = 1) ∧
    (¬ (∃ N, ∀ k ≥ N, partialQuotient a k = 1) →
      palindromicDensity (FactorTree.characteristicWord a) ≤ 2 - Real.sqrt 2) := by
  rw [characteristic_palindromicDensity ha ha' hirr]
  let s := slopeFractions a hirr
  exact ⟨density_eq_golden_reciprocal_iff s, fun h =>
    density_le_second_value_of_spectral_gap s (peak_gap_of_not_eventually_one s h)⟩

/-- The constant-tail value in cor:palSturm (5). -/
theorem characteristic_palindromicDensity_constant_tail {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) (d k₀ : Nat) (h : ∀ k ≥ k₀, partialQuotient a k = d) :
    palindromicDensity (FactorTree.characteristicWord a) =
      (1 + constantTailRoot d) / (2 + constantTailRoot d) := by
  rw [characteristic_palindromicDensity ha ha' hirr]
  exact density_constant_tail (slopeFractions a hirr) d k₀ h

end Thesis.SturmianDensity
