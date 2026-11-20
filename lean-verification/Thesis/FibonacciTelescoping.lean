import Thesis.FibonacciIdentities
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Thesis.Fibonacci

variable {K : Type*} [Field K] [CharZero K]

theorem fib_positive (n : Nat) : 0 < fib (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 0 < fib n + fib (n + 1)
    omega

private theorem fib_ne_zero {n : Nat} (hn : 0 < n) : (fib n : K) ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (fib_positive m))

def ratio (k : Nat) : K := (fib (k + 1) : K) / fib k

def previousRatio (k : Nat) : K := (fib (k - 1) : K) / fib k

/-- The ratio identity immediately following `lem:docagne`. -/
theorem docagne_ratio {k : Nat} (hk : 0 < k) (m : Nat) :
    (-1 : K) ^ k * fib m / ((fib k : K) * fib (k + m)) =
      ratio k - ratio (k + m) := by
  have hk' : (fib k : K) ≠ 0 := fib_ne_zero hk
  have hkm : (fib (k + m) : K) ≠ 0 := fib_ne_zero (by omega)
  have hd := congrArg (fun z : Int => (z : K)) (docagne k m)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, fibInt, Int.cast_natCast] at hd
  unfold ratio
  rw [div_sub_div _ _ hk' hkm, ← hd]
  congr 1
  ring

omit [CharZero K] in
private theorem telescoping_ranges (f : Nat → K) (a b : Nat) :
    (∑ i ∈ Finset.range b, (f i - f (a + i))) =
      (∑ i ∈ Finset.range a, f i) + (∑ i ∈ Finset.range b, f i) -
        ∑ i ∈ Finset.range (a + b), f i := by
  rw [Finset.sum_sub_distrib, Finset.sum_range_add]
  ring

/-- Proposition `prop:symm`. The range indices are shifted by one so the
sums have exactly the positive indices appearing in the thesis. -/
theorem fibonacci_sum_symmetry (a b : Nat) :
    (∑ i ∈ Finset.range b, (-1 : K) ^ (i + 1) * fib a /
      ((fib (i + 1) : K) * fib (i + 1 + a))) =
    ∑ i ∈ Finset.range a, (-1 : K) ^ (i + 1) * fib b /
      ((fib (i + 1) : K) * fib (i + 1 + b)) := by
  simp only [docagne_ratio (Nat.zero_lt_succ _) _]
  have hshift (x y : Nat) :
      (∑ i ∈ Finset.range y, (ratio (K := K) (i + 1) - ratio (i + 1 + x))) =
        (∑ i ∈ Finset.range x, ratio (i + 1)) + (∑ i ∈ Finset.range y, ratio (i + 1)) -
          ∑ i ∈ Finset.range (x + y), ratio (i + 1) := by
    have he (i : Nat) : x + i + 1 = i + 1 + x := by omega
    simpa only [he] using telescoping_ranges (fun i => ratio (K := K) (i + 1)) x y
  rw [hshift a b, hshift b a, Nat.add_comm b a]
  ac_rfl

omit [CharZero K] in
private theorem sign_even_mul (r : Nat) : (-1 : K) ^ (2 * r) = 1 := by
  rw [pow_mul]
  norm_num

def signedRatio (k : Nat) : K := (-1 : K) ^ k * ratio k

private theorem weighted_docagne {k : Nat} (hk : 0 < k) (r : Nat) :
    (fib (2 * r) : K) / ((fib k : K) * fib (k + 2 * r)) =
      signedRatio k - signedRatio (k + 2 * r) := by
  unfold signedRatio
  rw [pow_add (-1 : K) k (2 * r), sign_even_mul, mul_one, ← mul_sub,
    ← docagne_ratio hk (2 * r), ← mul_div_assoc, ← mul_assoc, ← mul_pow]
  norm_num

private theorem signed_ratio_pair (i : Nat) :
    signedRatio (K := K) (2 * i + 1) + signedRatio (2 * i + 2) =
      1 / ((fib (2 * i + 1) : K) * fib (2 * i + 2)) := by
  have h := docagne_ratio (K := K) (k := 2 * i + 1) (by omega) 1
  have hodd : (-1 : K) ^ (2 * i + 1) = -1 := by
    rw [pow_succ, sign_even_mul, one_mul]
  have heven : (-1 : K) ^ (2 * i + 2) = 1 := by
    rw [show 2 * i + 2 = 2 * (i + 1) by omega, sign_even_mul]
  unfold signedRatio
  rw [hodd, heven, one_mul, neg_one_mul]
  rw [hodd] at h
  simp only [show fib 1 = 1 by rfl, Nat.cast_one, mul_one] at h
  rw [neg_div] at h
  calc
    _ = -(ratio (K := K) (2 * i + 1) - ratio (2 * i + 2)) := by ring
    _ = _ := by rw [← h, neg_neg]

private theorem signed_ratio_sum (r : Nat) :
    (∑ i ∈ Finset.range (2 * r), signedRatio (K := K) (i + 1)) =
      ∑ i ∈ Finset.range r, 1 / ((fib (2 * i + 1) : K) * fib (2 * i + 2)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc, signed_ratio_pair]

/-- The finite telescoping formula in the proof of `prop:sum2r`.
The last sum is precisely the oscillating tail in that proof. -/
theorem even_shift_partial_sum (r N : Nat) :
    (fib (2 * r) : K) * (∑ i ∈ Finset.range N,
      1 / ((fib (i + 1) : K) * fib (i + 1 + 2 * r))) =
    (∑ i ∈ Finset.range r, 1 / ((fib (2 * i + 1) : K) * fib (2 * i + 2))) -
      ∑ i ∈ Finset.range (2 * r), signedRatio (N + i + 1) := by
  rw [Finset.mul_sum]
  simp only [mul_one_div, weighted_docagne (Nat.zero_lt_succ _) _]
  have h := telescoping_ranges (fun i => signedRatio (K := K) (i + 1)) (2 * r) N
  have he (i : Nat) : 2 * r + i + 1 = i + 1 + 2 * r := by omega
  simp only [he] at h
  change (∑ i ∈ Finset.range N,
      (signedRatio (K := K) (i + 1) - signedRatio (i + 1 + 2 * r))) = _
  rw [h, Nat.add_comm (2 * r) N, Finset.sum_range_add, signed_ratio_sum]
  ring

/-- The quotient step `lem:telesc` in the proof of the Millin formula. -/
theorem millin_step {n : Nat} (hn : 0 < n) :
    previousRatio (K := K) n - previousRatio (2 * n) = (-1 : K) ^ n / fib (2 * n) := by
  have hf : (fib n : K) ≠ 0 := fib_ne_zero hn
  have h2 : (fib (2 * n) : K) ≠ 0 := fib_ne_zero (by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hd := congrArg (fun z : Int => (z : K)) (millin_step_numerator k)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    fibInt, Int.cast_natCast] at hd
  unfold previousRatio
  rw [div_sub_div _ _ hf h2]
  have he : (fib (k + 1 - 1) : K) * fib (2 * (k + 1)) -
      (fib (k + 1) : K) * fib (2 * (k + 1) - 1) =
      (-1 : K) ^ (k + 1) * fib (k + 1) := by
    rw [show k + 1 - 1 = k by omega, mul_comm (fib (k + 1) : K)]
    exact hd
  rw [he]
  field_simp [hf, h2]
  ring

private theorem millin_signed_sum (m : Nat) (hm : 0 < m) (N : Nat) :
    (∑ i ∈ Finset.range N, (-1 : K) ^ (m * 2 ^ i) / fib (m * 2 ^ (i + 1))) =
      previousRatio m - previousRatio (m * 2 ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hp : 0 < m * 2 ^ N := Nat.mul_pos hm (Nat.two_pow_pos _)
    have hs := millin_step (K := K) hp
    have he : 2 * (m * 2 ^ N) = m * 2 ^ (N + 1) := by rw [Nat.pow_succ]; ac_rfl
    rw [he] at hs
    rw [← hs]
    ring

/-- The partial sum stated in `thm:millin`, including the correction
for the sign of the first term. -/
theorem millin_partial_sum (m : Nat) (hm : 0 < m) (N : Nat) :
    (∑ i ∈ Finset.range (N + 1), (1 : K) / fib (m * 2 ^ (i + 1))) =
      previousRatio m - previousRatio (m * 2 ^ (N + 1)) +
        (1 - (-1 : K) ^ m) / fib (2 * m) := by
  have hs := millin_signed_sum (K := K) m hm (N + 1)
  rw [Finset.sum_range_succ'] at hs ⊢
  have hsign (i : Nat) : (-1 : K) ^ (m * 2 ^ (i + 1)) = 1 := by
    rw [show m * 2 ^ (i + 1) = 2 * (m * 2 ^ i) by rw [Nat.pow_succ]; ac_rfl,
      sign_even_mul]
  simp only [hsign, pow_zero, mul_one] at hs
  have hfirst : m * 2 ^ (0 + 1) = 2 * m := by simp [Nat.mul_comm]
  rw [hfirst] at hs ⊢
  rw [← hs, sub_div]
  ring

end Thesis.Fibonacci
