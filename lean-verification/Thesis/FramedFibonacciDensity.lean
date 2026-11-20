import Thesis.FibonacciIdentities

namespace Thesis.Fibonacci

/-- Coefficients of `a + bφ` in the quadratic algebra with `φ² = φ + 1`. -/
structure GoldenInteger where
  constant : Int
  linear : Int
  deriving DecidableEq

namespace GoldenInteger

def ofInt (x : Int) : GoldenInteger := ⟨x, 0⟩

instance : Add GoldenInteger where
  add x y := ⟨x.constant + y.constant, x.linear + y.linear⟩

instance : Sub GoldenInteger where
  sub x y := ⟨x.constant - y.constant, x.linear - y.linear⟩

instance : Neg GoldenInteger where
  neg x := ⟨-x.constant, -x.linear⟩

instance : Mul GoldenInteger where
  mul x y :=
    ⟨x.constant * y.constant + x.linear * y.linear,
      x.constant * y.linear + x.linear * y.constant + x.linear * y.linear⟩

instance : OfNat GoldenInteger n where
  ofNat := ofInt n

private def power (x : GoldenInteger) : Nat → GoldenInteger
  | 0 => 1
  | n + 1 => x * power x n

instance : Pow GoldenInteger Nat where
  pow := power

def phi : GoldenInteger := ⟨0, 1⟩

def psi : GoldenInteger := 1 - phi

def phiInv : GoldenInteger := phi - 1

theorem phi_sq : phi * phi = phi + 1 := rfl

theorem phi_inv : phi * phiInv = 1 ∧ phiInv * phi = 1 := by decide

theorem phiInv_sq : phiInv * phiInv = 2 - phi := by decide

private theorem psi_mul (a b : Int) : psi * ⟨a, b⟩ = ⟨a - b, -a⟩ := by
  change GoldenInteger.mk (1 * a + (-1) * b)
    (1 * b + (-1) * a + (-1) * b) = GoldenInteger.mk (a - b) (-a)
  congr 1 <;> simp <;> omega

/-- The conjugate term in the Fibonacci ratio formula, given in the
coefficient basis `1, φ`. -/
theorem psi_power (n : Nat) : psi ^ n = ⟨fibInt (n + 1), -fibInt n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change psi * psi ^ n = _
    rw [ih, psi_mul]
    have hrec : fibInt (n + 2) = fibInt n + fibInt (n + 1) := by
      unfold fibInt
      rw [fib, Int.ofNat_add]
    rw [hrec]
    congr 1 <;> omega

end GoldenInteger

open GoldenInteger

/-- The exact error in `thm1Asymptotic` after multiplying by
`φ * (framed m).length`. All coefficients are verified in the quadratic
algebra, so the identity uses the relation `φ² = φ + 1` exactly. -/
theorem framed_density_error_numerator (m : Nat) :
    phi * ofInt ((framed m).count .a : Int) - ofInt ((framed m).length : Int) =
      -(phiInv * phiInv + psi ^ (m + 1)) := by
  rw [framed_count_a, framed_length, psi_power, phiInv_sq]
  change GoldenInteger.mk
    (0 * (fib (m + 1) + 1 : Nat) + 1 * 0 - (fib (m + 2) + 2 : Nat))
    (0 * 0 + 1 * (fib (m + 1) + 1 : Nat) + 1 * 0 - 0) =
    GoldenInteger.mk (-(2 - 0 + fibInt (m + 2))) (-(0 - 1 + -fibInt (m + 1)))
  simp only [Int.zero_mul, Int.one_mul, Int.zero_add, Int.add_zero, Int.sub_zero,
    Int.ofNat_add, fibInt]
  congr 1 <;> omega

end Thesis.Fibonacci
