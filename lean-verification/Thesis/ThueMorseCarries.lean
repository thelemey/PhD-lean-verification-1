import Thesis.ThueMorse
import Mathlib.RingTheory.Multiplicity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

namespace Thesis.ThueMorse

/-- The signed difference of digit sums, denoted by (c_m(n)) in the thesis. -/
def digitDelta (b m n : Nat) : ℤ := (digitSum b (n + m) : ℤ) - digitSum b n

/-- Removing one trailing zero lowers the exponent of divisibility by
one. The base need not be prime. -/
theorem trailingExponent_mul {b x : Nat} (hb : 1 < b) (hx : 0 < x) :
    multiplicity b (b * x) = multiplicity b x + 1 := by
  have hb0 : 0 < b := by omega
  have hf : FiniteMultiplicity b x := Nat.finiteMultiplicity_iff.2 ⟨by omega, hx⟩
  have hbf : FiniteMultiplicity b (b * x) :=
    Nat.finiteMultiplicity_iff.2 ⟨by omega, Nat.mul_pos hb0 hx⟩
  apply hbf.multiplicity_eq_iff.2
  constructor
  · rw [pow_succ']
    exact Nat.mul_dvd_mul_left b (pow_multiplicity_dvd _ _)
  · rw [pow_succ', Nat.mul_dvd_mul_iff_left hb0]
    exact (hf.pow_dvd_iff_le_multiplicity.not).2 (Nat.not_succ_le_self _)

/-- Adding one removes the trailing run of maximal digits, then
increments the next digit, as in `tw:lem(b)`. -/
theorem digitSum_succ_of_trailingExponent {b : Nat} (hb : 1 < b) (n : Nat) :
    (digitSum b (n + 1) : ℤ) =
      digitSum b n + 1 - ((b : ℤ) - 1) * multiplicity b (n + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    let q := n / b
    let r := n % b
    have hr : r < b := Nat.mod_lt _ (by omega)
    have hn : b * q + r = n := by
      simpa only [q, r, Nat.add_comm] using Nat.mod_add_div n b
    have hsum := digitSum_block hb q r hr
    rw [hn] at hsum
    by_cases hnr : r + 1 < b
    · have hpos : 0 < r + 1 := by omega
      have hn' : n + 1 = b * q + (r + 1) := by omega
      have hnd : ¬ b ∣ n + 1 := by
        rw [hn', Nat.dvd_iff_mod_eq_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hnr]
        omega
      rw [multiplicity_eq_zero.2 hnd, hn', digitSum_block hb q (r + 1) hnr, hsum]
      push_cast
      ring
    · have hlast : r = b - 1 := by omega
      have hn' : n + 1 = b * (q + 1) := by rw [Nat.mul_succ]; omega
      have hq : q < n := by
        apply Nat.div_lt_self _ hb
        by_contra! h
        have hn0 : n = 0 := Nat.eq_zero_of_le_zero h
        have hr0 : r = 0 := by simp [r, hn0]
        exact (Nat.sub_ne_zero_of_lt hb) (hlast.symm.trans hr0)
      have hrec := ih q hq
      rw [hn', trailingExponent_mul hb (Nat.succ_pos q)]
      have hd : digitSum b (b * (q + 1)) = digitSum b (q + 1) := by
        simpa using digitSum_block hb (q + 1) 0 (by omega)
      rw [hd, hrec, hsum, hlast]
      push_cast [Nat.cast_sub (show 1 ≤ b by omega)]
      ring

theorem digitDelta_succ_sub {b : Nat} (hb : 1 < b) (m n : Nat) :
    digitDelta b m (n + 1) - digitDelta b m n =
      -((b : ℤ) - 1) * ((multiplicity b (n + m + 1) : ℤ) - multiplicity b (n + 1)) := by
  unfold digitDelta
  rw [show n + 1 + m = n + m + 1 by omega,
    digitSum_succ_of_trailingExponent hb (n + m), digitSum_succ_of_trailingExponent hb n]
  ring

theorem digitDelta_scale {b : Nat} (hb : 1 < b) (m n r : Nat) (hr : r < b) :
    digitDelta b (b * m) (b * n + r) = digitDelta b m n := by
  unfold digitDelta
  rw [show b * n + r + b * m = b * (n + m) + r by rw [Nat.mul_add]; omega,
    digitSum_block hb _ _ hr, digitSum_block hb _ _ hr]
  push_cast
  ring

theorem digitDelta_small_no_carry {b q r μ : Nat} (hb : 1 < b) (h : r + μ < b) :
    digitDelta b μ (b * q + r) = μ := by
  unfold digitDelta
  rw [Nat.add_assoc, digitSum_block hb _ _ h, digitSum_block hb q r (by omega)]
  push_cast
  ring

theorem digitDelta_small_carry {b q r μ : Nat} (hb : 1 < b)
    (hr : r < b) (hμ : μ < b) (h : b ≤ r + μ) :
    digitDelta b μ (b * q + r) =
      (μ : ℤ) - ((b : ℤ) - 1) * (1 + multiplicity b (q + 1)) := by
  have hs : r + μ - b < b := by omega
  have he : b * q + r + μ = b * (q + 1) + (r + μ - b) := by rw [Nat.mul_succ]; omega
  unfold digitDelta
  rw [he, digitSum_block hb _ _ hs, digitSum_block hb _ _ hr]
  push_cast [Nat.cast_sub h]
  rw [digitSum_succ_of_trailingExponent hb]
  ring

end Thesis.ThueMorse
