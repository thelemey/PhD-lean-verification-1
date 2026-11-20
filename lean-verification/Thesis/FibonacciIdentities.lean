import Thesis.Fibonacci

namespace Thesis.Fibonacci

def fibInt (n : Nat) : Int := fib n

private theorem zfib_rec (n : Nat) : fibInt (n + 2) = fibInt n + fibInt (n + 1) := by
  unfold fibInt
  rw [fib, Int.ofNat_add]

/-- The integer form of d'Ocagne's identity (`lem:docagne`). The recurrence
also proves the boundary case `k = 0`. -/
theorem docagne (k m : Nat) :
    fibInt (k + m) * fibInt (k + 1) - fibInt (k + m + 1) * fibInt k =
      (-1 : Int) ^ k * fibInt m := by
  induction k with
  | zero =>
    simp only [Nat.zero_add]
    change fibInt m * 1 - fibInt (m + 1) * 0 = (-1 : Int) ^ 0 * fibInt m
    simp
  | succ k ih =>
    rw [show k + 1 + m = k + m + 1 by omega]
    rw [show k + m + 1 + 1 = (k + m) + 2 by omega, zfib_rec (k + m), zfib_rec k]
    rw [Int.pow_succ, Int.mul_neg, Int.mul_one, Int.neg_mul]
    simp only [Int.mul_add, Int.add_mul]
    omega

private theorem zfib_add (k : Nat) : ∀ m : Nat,
    fibInt (k + m + 1) = fibInt k * fibInt m + fibInt (k + 1) * fibInt (m + 1)
  | 0 => by
    change fibInt (k + 1) = fibInt k * 0 + fibInt (k + 1) * 1
    simp
  | 1 => by
    change fibInt (k + 2) = fibInt k * 1 + fibInt (k + 1) * 1
    simp [zfib_rec]
  | m + 2 => by
    have h1 := zfib_add k m
    have h2 := zfib_add k (m + 1)
    rw [show k + (m + 2) + 1 = (k + m + 1) + 2 by omega,
      zfib_rec (k + m + 1), zfib_rec m,
      show m + 2 + 1 = (m + 1) + 2 by omega, zfib_rec (m + 1)]
    rw [show k + m + 1 + 1 = k + (m + 1) + 1 by omega, h1, h2]
    simp only [Int.mul_add]
    omega

/-- Cassini's identity with the central index `k + 1`. -/
theorem cassini (k : Nat) :
    fibInt k * fibInt (k + 2) - fibInt (k + 1) * fibInt (k + 1) = (-1 : Int) ^ (k + 1) := by
  have h := docagne k 1
  change fibInt (k + 1) * fibInt (k + 1) - fibInt (k + 2) * fibInt k = (-1 : Int) ^ k * 1 at h
  rw [Int.mul_one] at h
  rw [Int.pow_succ, Int.mul_neg, Int.mul_one, Int.mul_comm (fibInt k) (fibInt (k + 2))]
  omega

/-- The numerator identity of `lem:telesc`, after clearing the two
Fibonacci denominators and writing its positive index as `k + 1`. -/
theorem millin_step_numerator (k : Nat) :
    fibInt k * fibInt (2 * (k + 1)) - fibInt (2 * (k + 1) - 1) * fibInt (k + 1) =
      (-1 : Int) ^ (k + 1) * fibInt (k + 1) := by
  have hEven : fibInt (2 * (k + 1)) = fibInt (k + 1) * (fibInt k + fibInt (k + 2)) := by
    rw [show 2 * (k + 1) = k + (k + 1) + 1 by omega, zfib_add k (k + 1), Int.mul_add]
    rw [Int.mul_comm (fibInt (k + 1)) (fibInt k)]
  have hOdd : fibInt (2 * (k + 1) - 1) = fibInt k * fibInt k + fibInt (k + 1) * fibInt (k + 1) := by
    rw [show 2 * (k + 1) - 1 = k + k + 1 by omega, zfib_add k k]
  rw [hEven, hOdd, ← cassini k]
  simp only [Int.mul_add, Int.add_mul, Int.sub_mul]
  have h1 : fibInt k * (fibInt (k + 1) * fibInt k) = fibInt k * fibInt k * fibInt (k + 1) := by ac_rfl
  have h2 : fibInt k * (fibInt (k + 1) * fibInt (k + 2)) =
      fibInt k * fibInt (k + 2) * fibInt (k + 1) := by ac_rfl
  rw [h1, h2]
  omega

end Thesis.Fibonacci
