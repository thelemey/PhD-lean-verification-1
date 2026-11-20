import Thesis.SturmianSemiconvergentRecords
import Thesis.SturmianDensityMeasure

open Set MeasureTheory Filter

namespace Thesis.SturmianDensity

/-- The constant-tail values in cor:palSturm for the actual word. -/
theorem characteristic_below_density_constant_tail {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) (d k₀ : Nat) (h : ∀ k ≥ k₀, partialQuotient a k = d)
    {p q : Nat} (hq : 0 < q) :
    BelowPalDensity (FactorTree.characteristicWord a) p q ↔
      (p : ℝ) / q < (1 + constantTailRoot d) / (2 + constantTailRoot d) := by
  rw [characteristic_below_density_iff ha ha' hirr hq,
    density_constant_tail (slopeFractions a hirr) d k₀ h]

theorem characteristic_inserted_below_density_iff {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) {p q : Nat} (hq : 0 < q) :
    BelowPalDensity (insertSeparator (FactorTree.characteristicWord a)) p q ↔
      (p : ℝ) / q < (slopeFractions a hirr).fischlerDensity :=
  (palDensity_insert _ p q).trans (characteristic_below_density_iff ha ha' hirr hq)

/-- The exceptional set defined by palindrome prefixes of the words. -/
def wordExceptionalSlopes : Set ℝ :=
  {a | a ∈ Ioo (0 : ℝ) 1 ∧ Irrational a ∧ BelowPalDensity (FactorTree.characteristicWord a) 1 2}

theorem wordExceptionalSlopes_eq : wordExceptionalSlopes = exceptionalSlopes := by
  ext a
  constructor
  · rintro ⟨⟨ha, ha'⟩, hirr, hp⟩
    have hd := (characteristic_below_density_iff ha ha' hirr (p := 1) (q := 2) (by decide)).1 hp
    exact ⟨⟨ha, ha'⟩, hirr, by simpa using hd⟩
  · rintro ⟨⟨ha, ha'⟩, hirr, hd⟩
    refine ⟨⟨ha, ha'⟩, hirr, (characteristic_below_density_iff ha ha' hirr (by decide)).2 ?_⟩
    simpa using hd

theorem wordExceptionalSlopes_eq_badlyApproximable :
    wordExceptionalSlopes = badlyApproximableSlopes :=
  wordExceptionalSlopes_eq.trans exceptional_slopes_eq_badly_approximable

/-- The measure and Hausdorff-dimension assertions for the actual
words, with the two cited classical metric theorems as premises. -/
theorem wordExceptionalSlopes_measure_and_dimension
    (hKhinchin : volume badlyApproximableSlopes = 0)
    (hJarnik : dimH badlyApproximableSlopes = 1) :
    volume wordExceptionalSlopes = 0 ∧ dimH wordExceptionalSlopes = 1 := by
  rw [wordExceptionalSlopes_eq]
  exact exceptional_slopes_measure_and_dimension hKhinchin hJarnik

theorem characteristic_word_density_ae_eq_half
    (hKhinchin : volume {a | a ∈ Ioo (0 : ℝ) 1 ∧
      ∃ ha : Irrational a, (slopeFractions a ha).BoundedQuotients} = 0) :
    ∀ᵐ a ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ p q : Nat, 0 < q →
      (BelowPalDensity (FactorTree.characteristicWord a) p q ↔ (p : ℝ) / q < 1 / 2) := by
  filter_upwards [density_ae_eq_half hKhinchin, ae_restrict_mem measurableSet_Ioo] with a h ha
  obtain ⟨hirr, hd⟩ := h
  intro p q hq
  rw [characteristic_below_density_iff ha.1 ha.2 hirr hq, hd]

end Thesis.SturmianDensity
