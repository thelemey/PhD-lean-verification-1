import Thesis.SturmianPalindromeRecords

namespace Thesis.SturmianDensity

/-- Two integer lattice points on opposite sides of an irrational
rotation, forming a basis of the integer lattice. -/
structure RotationRecordBracket (a : ℝ) where
  lowerTime : Nat
  upperTime : Nat
  lowerIndex : ℤ
  upperIndex : ℤ
  lowerTime_pos : 0 < lowerTime
  upperTime_pos : 0 < upperTime
  lower_pos : 0 < (lowerTime : ℝ) * a - lowerIndex
  upper_pos : 0 < (upperIndex : ℝ) - (upperTime : ℝ) * a
  width_le_one : (lowerTime : ℝ) * a - lowerIndex +
    ((upperIndex : ℝ) - (upperTime : ℝ) * a) ≤ 1
  determinant : (lowerTime : ℤ) * upperIndex - (upperTime : ℤ) * lowerIndex = 1

namespace RotationRecordBracket

variable {a : ℝ}

def lowerError (b : RotationRecordBracket a) : ℝ := (b.lowerTime : ℝ) * a - b.lowerIndex

def upperError (b : RotationRecordBracket a) : ℝ := (b.upperIndex : ℝ) - (b.upperTime : ℝ) * a

def nextTime (b : RotationRecordBracket a) : Nat := b.lowerTime + b.upperTime

private theorem error_pos (b : RotationRecordBracket a) :
    0 < b.lowerError ∧ 0 < b.upperError :=
  ⟨b.lower_pos, b.upper_pos⟩

/-- At any earlier positive time, the signed error from an integer
cannot improve either side at once. A point with both coordinates
positive in the lattice basis would be at or beyond the next time. -/
theorem no_smaller_error_before_sum (b : RotationRecordBracket a) {t : Nat}
    (ht : 0 < t) (ht' : t < b.nextTime) (p : ℤ) :
    (t : ℝ) * a - p ≤ -b.upperError ∨ b.lowerError ≤ (t : ℝ) * a - p := by
  let u : ℤ := (t : ℤ) * b.upperIndex - p * (b.upperTime : ℤ)
  let v : ℤ := p * (b.lowerTime : ℤ) - (t : ℤ) * b.lowerIndex
  have htZ : (t : ℤ) = u * (b.lowerTime : ℤ) + v * (b.upperTime : ℤ) := by
    dsimp only [u, v]
    calc
      _ = (t : ℤ) * ((b.lowerTime : ℤ) * b.upperIndex - (b.upperTime : ℤ) * b.lowerIndex) := by
        rw [b.determinant, mul_one]
      _ = _ := by ring
  have hpZ : p = u * b.lowerIndex + v * b.upperIndex := by
    dsimp only [u, v]
    calc
      _ = p * ((b.lowerTime : ℤ) * b.upperIndex - (b.upperTime : ℤ) * b.lowerIndex) := by
        rw [b.determinant, mul_one]
      _ = _ := by ring
  have htR : (t : ℝ) = (u : ℝ) * b.lowerTime + (v : ℝ) * b.upperTime := by exact_mod_cast htZ
  have hpR : (p : ℝ) = (u : ℝ) * b.lowerIndex + (v : ℝ) * b.upperIndex := by exact_mod_cast hpZ
  have herr : (t : ℝ) * a - p = (u : ℝ) * b.lowerError - (v : ℝ) * b.upperError := by
    rw [htR, hpR, lowerError, upperError]
    ring
  have hl : 0 < (b.lowerTime : ℝ) := by exact_mod_cast b.lowerTime_pos
  have hr : 0 < (b.upperTime : ℝ) := by exact_mod_cast b.upperTime_pos
  have hpos : 0 < (t : ℝ) := by exact_mod_cast ht
  have hlt : (t : ℝ) < (b.lowerTime : ℝ) + b.upperTime := by
    exact_mod_cast (show t < b.lowerTime + b.upperTime from ht')
  obtain ⟨hL, hU⟩ := b.error_pos
  by_cases hu : 0 < u <;> by_cases hv : 0 < v
  · have hu' : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
    have hv' : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
    have h₁ := mul_le_mul_of_nonneg_right hu' hl.le
    have h₂ := mul_le_mul_of_nonneg_right hv' hr.le
    exfalso
    linarith
  · right
    have hu' : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
    have hv' : (v : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hv)
    rw [herr]
    have h₁ := mul_le_mul_of_nonneg_right hu' hL.le
    have h₂ := mul_nonpos_of_nonpos_of_nonneg hv' hU.le
    linarith
  · left
    have hu' : (u : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hu)
    have hv' : (1 : ℝ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
    rw [herr]
    have h₁ := mul_nonpos_of_nonpos_of_nonneg hu' hL.le
    have h₂ := mul_le_mul_of_nonneg_right hv' hU.le
    linarith
  · have hu' : (u : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hu)
    have hv' : (v : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hv)
    have h₁ := mul_nonpos_of_nonpos_of_nonneg hu' hl.le
    have h₂ := mul_nonpos_of_nonpos_of_nonneg hv' hr.le
    exfalso
    linarith

theorem fractional_bounds_before_sum (b : RotationRecordBracket a) {t : Nat}
    (ht : 0 < t) (ht' : t < b.nextTime) :
    b.lowerError ≤ Int.fract ((t : ℝ) * a) ∧
      Int.fract ((t : ℝ) * a) ≤ 1 - b.upperError := by
  let x := (t : ℝ) * a
  obtain ⟨hL, hU⟩ := b.error_pos
  have h₁ := b.no_smaller_error_before_sum ht ht' (Int.floor x)
  have h₂ := b.no_smaller_error_before_sum ht ht' (Int.floor x + 1)
  change Int.fract x ≤ -b.upperError ∨ b.lowerError ≤ Int.fract x at h₁
  rw [Int.cast_add, Int.cast_one, ← sub_sub] at h₂
  change Int.fract x - 1 ≤ -b.upperError ∨ b.lowerError ≤ Int.fract x - 1 at h₂
  exact ⟨h₁.resolve_left (by linarith [Int.fract_nonneg x]),
    by have h := h₂.resolve_right (by linarith [Int.fract_lt_one x]); linarith⟩

theorem time_cast_eq (b : RotationRecordBracket a) :
    (b.nextTime : ℝ) * a - (b.lowerIndex + b.upperIndex : ℤ) =
      b.lowerError - b.upperError := by
  simp only [nextTime, lowerError, upperError, Nat.cast_add, Int.cast_add]
  ring

/-- The next record time is the sum of the two previous times. Its
fractional part is a new minimum or a new maximum according to the
sign of the difference of the signed distances. -/
theorem record_at_sum (b : RotationRecordBracket a) (ha : Irrational a) :
    (∀ t : Nat, 0 < t → t < b.nextTime →
      Int.fract ((b.nextTime : ℝ) * a) < Int.fract ((t : ℝ) * a)) ∨
    (∀ t : Nat, 0 < t → t < b.nextTime →
      Int.fract ((t : ℝ) * a) < Int.fract ((b.nextTime : ℝ) * a)) := by
  let X := (b.nextTime : ℝ) * a
  let p := b.lowerIndex + b.upperIndex
  have herror : X - p = b.lowerError - b.upperError := b.time_cast_eq
  obtain ⟨hL, hU⟩ := b.error_pos
  have hw : b.lowerError + b.upperError ≤ 1 := b.width_le_one
  have hne : X ≠ (p : ℝ) :=
    (irrational_natCast_mul_iff.2 ⟨Nat.ne_of_gt
      (Nat.add_pos_left b.lowerTime_pos _), ha⟩).ne_int p
  rcases lt_or_gt_of_ne hne with h | h
  · right
    have hfloor : ⌊X⌋ = p - 1 := by
      apply Int.floor_eq_iff.2
      push_cast
      exact ⟨by linarith, by linarith⟩
    have hf : Int.fract X = 1 + b.lowerError - b.upperError := by
      rw [Int.fract, hfloor, Int.cast_sub, Int.cast_one]
      linarith
    intro t ht hlt
    have hbnd := (b.fractional_bounds_before_sum ht hlt).2
    change _ < Int.fract X
    linarith
  · left
    have hfloor : ⌊X⌋ = p := Int.floor_eq_iff.2 ⟨h.le, by linarith⟩
    have hf : Int.fract X = b.lowerError - b.upperError := by
      rw [Int.fract, hfloor, herror]
    intro t ht hlt
    have hbnd := (b.fractional_bounds_before_sum ht hlt).1
    change Int.fract X < _
    linarith

end RotationRecordBracket
end Thesis.SturmianDensity
