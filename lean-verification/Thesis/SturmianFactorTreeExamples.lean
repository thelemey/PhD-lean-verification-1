import Thesis.SturmianFactorTree
import Mathlib.Data.Real.GoldenRatio

open scoped goldenRatio

namespace Thesis.FactorTree

/-- For these slopes, the first d letters are zero and the next is one. -/
theorem characteristic_initial_zero_run {a : ℝ} (ha : 0 < a) (ha' : a < 1) (d : Nat)
    (hl : ((d : ℝ) + 1) * a < 1) (hr : 1 ≤ ((d : ℝ) + 2) * a) :
    (∀ i < d, characteristicWord a i = false) ∧ characteristicWord a d = true := by
  have hsmall (j : ℝ) (hj : 0 ≤ j) (hj' : j ≤ (d : ℝ) + 1) : ⌊j * a⌋ = 0 :=
    Int.floor_eq_zero_iff.2 ⟨mul_nonneg hj ha.le, (mul_le_mul_of_nonneg_right hj' ha.le).trans_lt hl⟩
  constructor
  · intro i hi
    have hid : (i : ℝ) + 1 ≤ d := by exact_mod_cast Nat.succ_le_of_lt hi
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
    rw [characteristic_letter_floor_eq, hsmall _ (by linarith) (by linarith),
      hsmall _ (by linarith) (by linarith)]
    decide
  · have hbig : ⌊((d : ℝ) + 2) * a⌋ = 1 := by
      apply Int.floor_eq_iff.2
      constructor
      · simpa using hr
      · norm_num
        linarith
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    rw [characteristic_letter_floor_eq, hbig, hsmall _ (by linarith) le_rfl]
    decide

private noncomputable def exampleSlope (d : Nat) : ℝ :=
  1 / ((d : ℝ) + φ)

private theorem exampleSlope_properties (d : Nat) :
    0 < exampleSlope d ∧ exampleSlope d < 1 ∧ Irrational (exampleSlope d) ∧
      ((d : ℝ) + 1) * exampleSlope d < 1 ∧ 1 ≤ ((d : ℝ) + 2) * exampleSlope d := by
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hz : 0 < (d : ℝ) + φ := by linarith [one_lt_gold]
  change 0 < 1 / ((d : ℝ) + φ) ∧ 1 / ((d : ℝ) + φ) < 1 ∧
    Irrational (1 / ((d : ℝ) + φ)) ∧ ((d : ℝ) + 1) * (1 / ((d : ℝ) + φ)) < 1 ∧
      1 ≤ ((d : ℝ) + 2) * (1 / ((d : ℝ) + φ))
  rw [mul_one_div, mul_one_div]
  refine ⟨one_div_pos.mpr hz, (div_lt_one hz).2 (by linarith [one_lt_gold]), ?_,
    (div_lt_one hz).2 (by linarith [one_lt_gold]), (one_le_div hz).2 (by linarith [gold_lt_two])⟩
  rw [one_div, irrational_inv_iff, irrational_natCast_add_iff]
  exact gold_irrational

/-- Every row of the table is realized by a characteristic word, with
an explicit irrational slope for each initial run length. -/
theorem depth_eight_table_realized {d : Nat} (hd : 0 < d) (hd' : d ≤ 4) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ Irrational a ∧
      (∀ i < d, characteristicWord a i = false) ∧ characteristicWord a d = true ∧
      (d, (factorVertices (characteristicWord a) 8).card, albertsonOfWord (characteristicWord a) 8,
      quadraticAlbertsonOfWord (characteristicWord a) 8, firstZagrebOfWord (characteristicWord a) 8,
      secondZagrebOfWord (characteristicWord a) 8) ∈ depthEightTable := by
  obtain ⟨ha, ha', hirr, hl, hr⟩ := exampleSlope_properties d
  obtain ⟨hrun, hchange⟩ := characteristic_initial_zero_run ha ha' d hl hr
  refine ⟨exampleSlope d, ha, ha', hirr, hrun, hchange, ?_⟩
  exact characteristic_depth_eight_table_row ha ha' hirr hd hd' false hrun (by simp [hchange])

/-- The Fibonacci case stated after thm:factortree, at the slope 1/φ²
used to define the Fibonacci word in defffFibonaccin. -/
theorem fibonacci_factor_tree_indices (n : Nat) (hn : 3 ≤ n) :
    let w := characteristicWord (1 / φ ^ 2)
    albertsonOfWord w n = 4 * (n : ℤ) - 2 ∧
    quadraticAlbertsonOfWord w n = 18 * (n : ℤ) - 12 ∧
    secondZagrebOfWord w n = 2 * (n : ℤ) ^ 2 + 10 * n - 10 := by
  have he : exampleSlope 1 = 1 / φ ^ 2 := by
    unfold exampleSlope
    rw [Nat.cast_one, gold_sq, add_comm φ 1]
  obtain ⟨ha, ha', hirr, hl, hr⟩ := exampleSlope_properties 1
  obtain ⟨hrun, hchange⟩ := characteristic_initial_zero_run ha ha' 1 hl hr
  have hchange' : characteristicWord (exampleSlope 1) 1 ≠ false := by
    rw [hchange]
    decide
  obtain ⟨_, h₁, h₂, _, h₃⟩ :=
    characteristic_factor_tree_indices ha ha' hirr (n := n) (by decide : 0 < (1 : Nat)) hn false hrun hchange'
  rw [he] at h₁ h₂ h₃
  dsimp only
  norm_num only [Nat.cast_one, mul_one] at h₁ h₂ h₃
  exact ⟨h₁, by omega, by omega⟩

end Thesis.FactorTree
