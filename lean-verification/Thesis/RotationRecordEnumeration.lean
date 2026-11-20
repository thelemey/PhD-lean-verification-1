import Thesis.RotationRecordBrackets
import Mathlib.Data.Nat.Find

namespace Thesis.SturmianDensity

def FractionalRecord (a : ℝ) (j : Nat) : Prop :=
  (∀ i : Nat, 0 < i → i < j → Int.fract ((j : ℝ) * a) < Int.fract ((i : ℝ) * a)) ∨
  (∀ i : Nat, 0 < i → i < j → Int.fract ((i : ℝ) * a) < Int.fract ((j : ℝ) * a))

namespace RotationRecordBracket

variable {a : ℝ}

private theorem lower_fraction (b : RotationRecordBracket a) :
    Int.fract ((b.lowerTime : ℝ) * a) = b.lowerError := by
  have h₁ := b.lower_pos
  have h₂ := b.upper_pos
  have h₃ := b.width_le_one
  have h : ⌊(b.lowerTime : ℝ) * a⌋ = b.lowerIndex :=
    Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩
  rw [Int.fract, h, lowerError]

private theorem upper_fraction (b : RotationRecordBracket a) :
    Int.fract ((b.upperTime : ℝ) * a) = 1 - b.upperError := by
  have h₁ := b.lower_pos
  have h₂ := b.upper_pos
  have h₃ := b.width_le_one
  have h : ⌊(b.upperTime : ℝ) * a⌋ = b.upperIndex - 1 := by
    apply Int.floor_eq_iff.2
    push_cast
    exact ⟨by linarith, by linarith⟩
  rw [Int.fract, h, Int.cast_sub, Int.cast_one, upperError]
  ring

theorem not_record_between (b : RotationRecordBracket a) {t : Nat}
    (hlt : max b.lowerTime b.upperTime < t) (hnext : t < b.nextTime) :
    ¬FractionalRecord a t := by
  have hL : b.lowerTime < t := (le_max_left _ _).trans_lt hlt
  have hU : b.upperTime < t := (le_max_right _ _).trans_lt hlt
  have bounds := b.fractional_bounds_before_sum (b.lowerTime_pos.trans hL) hnext
  rintro (h | h)
  · have hh := h b.lowerTime b.lowerTime_pos hL
    rw [b.lower_fraction] at hh
    exact (not_lt_of_ge bounds.1) hh
  · have hh := h b.upperTime b.upperTime_pos hU
    rw [b.upper_fraction] at hh
    exact (not_lt_of_ge bounds.2) hh

private theorem errors_ne (b : RotationRecordBracket a) (ha : Irrational a) :
    b.lowerError ≠ b.upperError := by
  intro he
  have h := b.time_cast_eq
  rw [he, sub_self, sub_eq_zero] at h
  have hpos : b.nextTime ≠ 0 := (Nat.add_pos_left b.lowerTime_pos _).ne'
  exact (irrational_natCast_mul_iff.2 ⟨hpos, ha⟩).ne_int _ h

/-- Advance to the new record by replacing the side whose error was larger. -/
noncomputable def advance (b : RotationRecordBracket a) (ha : Irrational a) :
    RotationRecordBracket a := by
  by_cases h : b.upperError < b.lowerError
  · refine ⟨b.nextTime, b.upperTime, b.lowerIndex + b.upperIndex, b.upperIndex,
      Nat.add_pos_left b.lowerTime_pos _, b.upperTime_pos, ?_, b.upper_pos, ?_, ?_⟩
    · rw [b.time_cast_eq]
      exact sub_pos.2 h
    · rw [b.time_cast_eq]
      have h₁ := b.width_le_one
      have h₂ := b.upper_pos
      change b.lowerError - b.upperError + b.upperError ≤ 1
      change b.lowerError + b.upperError ≤ 1 at h₁
      change 0 < b.upperError at h₂
      linarith
    · simp only [nextTime, Nat.cast_add]
      calc
        _ = (b.lowerTime : ℤ) * b.upperIndex - (b.upperTime : ℤ) * b.lowerIndex := by ring
        _ = 1 := b.determinant
  · have hlt : b.lowerError < b.upperError := lt_of_le_of_ne (le_of_not_gt h) (b.errors_ne ha)
    refine ⟨b.lowerTime, b.nextTime, b.lowerIndex, b.lowerIndex + b.upperIndex,
      b.lowerTime_pos, Nat.add_pos_right _ b.upperTime_pos, b.lower_pos, ?_, ?_, ?_⟩
    · have he := b.time_cast_eq
      linarith
    · have he := b.time_cast_eq
      have h₁ := b.width_le_one
      have h₂ := b.lower_pos
      change b.lowerError + ((b.lowerIndex + b.upperIndex : ℤ) -
        (b.nextTime : ℝ) * a) ≤ 1
      change b.lowerError + b.upperError ≤ 1 at h₁
      change 0 < b.lowerError at h₂
      linarith
    · simp only [nextTime, Nat.cast_add]
      calc
        _ = (b.lowerTime : ℤ) * b.upperIndex - (b.upperTime : ℤ) * b.lowerIndex := by ring
        _ = 1 := b.determinant

theorem advance_max (b : RotationRecordBracket a) (ha : Irrational a) :
    max (b.advance ha).lowerTime (b.advance ha).upperTime = b.nextTime := by
  unfold advance
  split_ifs
  · exact max_eq_left (Nat.le_add_left _ _)
  · exact max_eq_right (Nat.le_add_right _ _)

theorem advance_nextTime_gt (b : RotationRecordBracket a) (ha : Irrational a) :
    b.nextTime < (b.advance ha).nextTime := by
  unfold advance
  split_ifs
  · exact Nat.lt_add_of_pos_right b.upperTime_pos
  · exact Nat.lt_add_of_pos_left b.lowerTime_pos

end RotationRecordBracket

private def initialBracket {a : ℝ} (ha : 0 < a) (ha' : a < 1) : RotationRecordBracket a where
  lowerTime := 1
  upperTime := 1
  lowerIndex := 0
  upperIndex := 1
  lowerTime_pos := Nat.zero_lt_one
  upperTime_pos := Nat.zero_lt_one
  lower_pos := by simpa using ha
  upper_pos := by simpa using (sub_pos.2 ha')
  width_le_one := by simp
  determinant := by decide

private noncomputable def bracketSequence {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a) :
    Nat → RotationRecordBracket a
  | 0 => initialBracket ha ha'
  | n + 1 => (bracketSequence ha ha' hirr n).advance hirr

/-- Increasing times of the successive new records of the irrational rotation. -/
noncomputable def recordTime {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a) (n : Nat) : Nat :=
  (bracketSequence ha ha' hirr n).nextTime

theorem recordTime_strictMono {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a) :
    StrictMono (recordTime ha ha' hirr) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (bracketSequence ha ha' hirr n).advance_nextTime_gt hirr

theorem fractionalRecord_iff_exists_time {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a)
    {t : Nat} (ht : 1 < t) :
    FractionalRecord a t ↔ ∃ n, recordTime ha ha' hirr n = t := by
  constructor
  · intro hrecord
    let R := recordTime ha ha' hirr
    have hex : ∃ n, t ≤ R n := by
      obtain ⟨n, hn⟩ := ((recordTime_strictMono ha ha' hirr).tendsto_atTop.eventually_ge_atTop t).exists
      exact ⟨n, hn⟩
    let n := Nat.find hex
    have hn : t ≤ R n := Nat.find_spec hex
    have hlate : ∀ i < n, R i < t := fun i hi => Nat.lt_of_not_ge (Nat.find_min hex hi)
    let b := bracketSequence ha ha' hirr n
    have hmax : max b.lowerTime b.upperTime < t := by
      cases hn' : n with
      | zero => simpa [b, hn', bracketSequence, initialBracket] using ht
      | succ i =>
        have hprev : R i < t := hlate i (by omega)
        change (bracketSequence ha ha' hirr i).nextTime < t at hprev
        dsimp only [b]
        rw [hn']
        change max ((bracketSequence ha ha' hirr i).advance hirr).lowerTime
          ((bracketSequence ha ha' hirr i).advance hirr).upperTime < t
        rwa [RotationRecordBracket.advance_max]
    refine ⟨n, le_antisymm ?_ hn⟩
    exact Nat.le_of_not_gt (fun hgt => b.not_record_between hmax hgt hrecord)
  · rintro ⟨n, rfl⟩
    exact (bracketSequence ha ha' hirr n).record_at_sum hirr

/-- Exact recursive enumeration of the characteristic word's
palindromic prefixes by the two-sided rotation record algorithm. -/
theorem characteristic_palPrefix_iff_recordTime {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) (n : Nat) :
    PalPrefix (FactorTree.characteristicWord a) n ↔
      ∃ i, recordTime ha ha' hirr i = n + 2 :=
  (characteristic_palPrefix_iff_fractional_record ha ha' hirr n).trans
    (fractionalRecord_iff_exists_time ha ha' hirr (by omega))

end Thesis.SturmianDensity
