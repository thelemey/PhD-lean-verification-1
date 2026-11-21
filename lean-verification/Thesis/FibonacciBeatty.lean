import Thesis.FibonacciMechanical
import Mathlib.NumberTheory.Rayleigh

open Set
open scoped goldenRatio Pointwise

namespace Thesis.Fibonacci

private theorem gold_sq_pos : 0 < φ ^ 2 := by positivity

private theorem gold_sq_irrational : Irrational (φ ^ 2) := by
  rw [gold_sq]
  simpa using gold_irrational.add_ratCast 1

/-- Positions are one-based in the Beatty sequences of `lem:mechanical`. -/
theorem infiniteWord_b_iff_beatty (i : Nat) :
    infiniteWord i = .b ↔ ∃ m : ℤ, 0 < m ∧ beattySeq (φ ^ 2) m = (i : ℤ) + 1 := by
  rw [infiniteWord_letter_floor]
  let x := ((i : ℝ) + 1) * mechanicalSlope
  let y := ((i : ℝ) + 2) * mechanicalSlope
  change ⌊y⌋ = ⌊x⌋ + 1 ↔ _
  have hxy : y < x + 1 := by
    dsimp [x, y]
    linarith [mechanicalSlope_lt_one]
  have hx : 0 < x := by dsimp [x]; exact mul_pos (by positivity) mechanicalSlope_pos
  have hx' : x = ((i : ℝ) + 1) / (φ ^ 2) := by simp [x, mechanicalSlope, div_eq_mul_inv]
  have hy' : y = ((i : ℝ) + 2) / (φ ^ 2) := by simp [y, mechanicalSlope, div_eq_mul_inv]
  have hirr (m : ℤ) (hm : 0 < m) : Irrational ((m : ℝ) * φ ^ 2) :=
    gold_sq_irrational.intCast_mul hm.ne'
  constructor
  · intro h
    let m := ⌊x⌋ + 1
    have hxm : x < (m : ℝ) := by simp [m, Int.lt_floor_add_one]
    have hmy : (m : ℝ) ≤ y := by simpa only [h] using Int.floor_le y
    have hm : 0 < m := by exact_mod_cast hx.trans hxm
    refine ⟨m, hm, ?_⟩
    rw [hx', div_lt_iff₀ gold_sq_pos] at hxm
    rw [hy', le_div_iff₀ gold_sq_pos] at hmy
    apply Int.floor_eq_iff.2
    push_cast
    have hne : (m : ℝ) * φ ^ 2 ≠ (i : ℝ) + 2 := by
      simpa using (hirr m hm).ne_int ((i : ℤ) + 2)
    exact ⟨hxm.le, by linarith [hmy.lt_of_ne hne]⟩
  · rintro ⟨m, hm, he⟩
    have hf := Int.floor_eq_iff.1 he
    push_cast at hf
    have hne : (m : ℝ) * φ ^ 2 ≠ (i : ℝ) + 1 := by
      simpa using (hirr m hm).ne_int ((i : ℤ) + 1)
    have hxm : x < (m : ℝ) := by
      rw [hx', div_lt_iff₀ gold_sq_pos]
      exact hf.1.lt_of_ne hne.symm
    have hmy : (m : ℝ) ≤ y := by
      rw [hy', le_div_iff₀ gold_sq_pos]
      linarith [hf.2]
    have h₁ := Int.floor_lt.2 hxm
    have h₂ := Int.le_floor.2 hmy
    have h₃ : ⌊y⌋ ≤ ⌊x⌋ + 1 := by
      apply Int.floor_le_iff.2
      push_cast
      linarith [Int.lt_floor_add_one x]
    omega

theorem infiniteWord_a_iff_beatty (i : Nat) :
    infiniteWord i = .a ↔ ∃ m : ℤ, 0 < m ∧ beattySeq φ m = (i : ℤ) + 1 := by
  have hc : Real.HolderConjugate φ (φ ^ 2) := Real.holderConjugate_iff.2
    ⟨one_lt_gold, by rw [add_comm, ← one_div]; exact mechanicalSlope_add_inv_gold⟩
  have hp : (i : ℤ) + 1 ∈ {n : ℤ | 0 < n} := by simp
  rw [← gold_irrational.beattySeq_symmDiff_beattySeq_pos hc, mem_symmDiff] at hp
  rcases hp with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · have he : infiniteWord i ≠ .b := fun h => hb ((infiniteWord_b_iff_beatty i).1 h)
    cases h : infiniteWord i with
    | a => exact ⟨fun _ => ha, fun _ => rfl⟩
    | b => exact (he h).elim
  · rw [(infiniteWord_b_iff_beatty i).2 hb]
    constructor
    · intro h
      cases h
    · exact fun h => (ha h).elim

/-- The positions of consecutive ones differ by two or three. -/
theorem golden_beatty_gaps (m : ℤ) :
    beattySeq (φ ^ 2) (m + 1) - beattySeq (φ ^ 2) m = 2 ∨
    beattySeq (φ ^ 2) (m + 1) - beattySeq (φ ^ 2) m = 3 := by
  have hf : ⌊φ ^ 2⌋ = 2 := Int.floor_eq_iff.2 (by
    push_cast
    rw [gold_sq]
    exact ⟨by linarith [one_lt_gold], by linarith [gold_lt_two]⟩)
  have hl := Int.le_floor_add ((m : ℝ) * φ ^ 2) (φ ^ 2)
  have hu := Int.le_floor_add_floor ((m : ℝ) * φ ^ 2) (φ ^ 2)
  rw [hf] at hl hu
  simp only [beattySeq, Int.cast_add, Int.cast_one, add_mul, one_mul]
  omega

private theorem beatty_monotone : Monotone (beattySeq (φ ^ 2)) := by
  intro m n h
  apply Int.floor_mono
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) gold_sq_pos.le

theorem infiniteWord_no_bb (i : Nat) :
    ¬ (infiniteWord i = .b ∧ infiniteWord (i + 1) = .b) := by
  rintro ⟨hi, hj⟩
  obtain ⟨m, _, hm⟩ := (infiniteWord_b_iff_beatty i).1 hi
  obtain ⟨n, _, hn⟩ := (infiniteWord_b_iff_beatty (i + 1)).1 hj
  push_cast at hn
  have hmn : m < n := by
    by_contra! h
    have he := beatty_monotone h
    omega
  have hn' := beatty_monotone (show m + 1 ≤ n by omega)
  have hg := golden_beatty_gaps m
  omega

private theorem beatty_brackets_position (i : Nat) :
    ∃ m : ℤ, 0 ≤ m ∧ beattySeq (φ ^ 2) m < (i : ℤ) + 1 ∧
      (i : ℤ) + 1 ≤ beattySeq (φ ^ 2) (m + 1) := by
  let x := ((i : ℝ) + 1) * mechanicalSlope
  have hx : 0 ≤ x := by dsimp [x]; exact mul_nonneg (by positivity) mechanicalSlope_pos.le
  have hxd : x = ((i : ℝ) + 1) / (φ ^ 2) := by simp [x, mechanicalSlope, div_eq_mul_inv]
  have hxi : Irrational x := by
    dsimp [x]
    rw [← Nat.cast_add_one]
    exact mechanicalSlope_irrational.natCast_mul (Nat.succ_ne_zero i)
  have hlo : (⌊x⌋ : ℝ) < x := (Int.floor_le x).lt_of_ne (hxi.ne_int _).symm
  have hhi := Int.lt_floor_add_one x
  have hlo' := (lt_div_iff₀ gold_sq_pos).1 (hlo.trans_eq hxd)
  have hhi' := (div_lt_iff₀ gold_sq_pos).1 (hxd.symm.trans_lt hhi)
  refine ⟨⌊x⌋, Int.floor_nonneg.2 hx, Int.floor_lt.2 ?_, Int.le_floor.2 ?_⟩
  · push_cast
    exact hlo'
  · push_cast
    exact hhi'.le

/-- At most two zeros occur between successive ones, including before the first one. -/
theorem infiniteWord_has_b_in_three (i : Nat) :
    infiniteWord i = .b ∨ infiniteWord (i + 1) = .b ∨ infiniteWord (i + 2) = .b := by
  obtain ⟨m, hm, hlo, hhi⟩ := beatty_brackets_position i
  have hg := golden_beatty_gaps m
  have he : beattySeq (φ ^ 2) (m + 1) = (i : ℤ) + 1 ∨
      beattySeq (φ ^ 2) (m + 1) = (i : ℤ) + 2 ∨
      beattySeq (φ ^ 2) (m + 1) = (i : ℤ) + 3 := by omega
  rcases he with h | h | h
  · exact Or.inl ((infiniteWord_b_iff_beatty i).2 ⟨m + 1, by omega, h⟩)
  · exact Or.inr (Or.inl ((infiniteWord_b_iff_beatty (i + 1)).2
      ⟨m + 1, by omega, by push_cast; omega⟩))
  · exact Or.inr (Or.inr ((infiniteWord_b_iff_beatty (i + 2)).2
      ⟨m + 1, by omega, by push_cast; omega⟩))

private theorem factorWindow_three (i : Nat) :
    factorWindow i 3 = [infiniteWord i, infiniteWord (i + 1), infiniteWord (i + 2)] := by
  change List.ofFn _ = _
  simp [List.ofFn_succ, Nat.add_assoc]

/-- The classification in `lem:local`, with the four witnesses in the prefix 01001010. -/
theorem length_three_factors (v : List Letter) :
    (∃ i, factorWindow i 3 = v) ↔
      v = [.a, .a, .b] ∨ v = [.a, .b, .a] ∨
      v = [.b, .a, .a] ∨ v = [.b, .a, .b] := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [factorWindow_three]
    have h₁ := infiniteWord_no_bb i
    have h₂ : ¬ (infiniteWord (i + 1) = .b ∧ infiniteWord (i + 2) = .b) :=
      infiniteWord_no_bb (i + 1)
    have h₃ := infiniteWord_has_b_in_three i
    cases ha : infiniteWord i <;> cases hb : infiniteWord (i + 1) <;>
      cases hc : infiniteWord (i + 2) <;> simp_all
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨2, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨4, by decide⟩

end Thesis.Fibonacci
