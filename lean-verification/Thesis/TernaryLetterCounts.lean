import Thesis.TernaryWord
import Thesis.FibonacciTableLimit
import Thesis.FibonacciTelescoping

open Filter Topology Real
open scoped goldenRatio

namespace Thesis.TernaryWord

open Fibonacci (fib)

/-- F_(n-1) with the source's explicit F_(-1) = 1 at n = 0. -/
def precedingFib : ℕ → ℕ
  | 0 => 1
  | n+1 => fib n

private theorem precedingFib_step (n : ℕ) :
    precedingFib (n+2) = precedingFib (n+1) + precedingFib n := by
  cases n with
  | zero => rfl
  | succ n => exact Nat.add_comm _ _

/-- All three counts from the base words and the concatenation recurrence,
as in the proof of lemmanovelwordn1. -/
theorem letter_counts : ∀ n : ℕ,
    (word n).count none = fib (n+1) ∧
    (word n).count (some .b) = precedingFib n ∧ (word n).count (some .a) = fib n
  | 0 => by decide
  | 1 => by decide
  | n+2 => by
    obtain ⟨z₁,b₁,a₁⟩ := letter_counts (n+1)
    obtain ⟨z₀,b₀,a₀⟩ := letter_counts n
    simp only [word, List.count_append, z₁,b₁,a₁,z₀,b₀,a₀, precedingFib_step]
    exact ⟨Nat.add_comm _ _, trivial, Nat.add_comm _ _⟩

theorem length_ratio_tendsto :
    Tendsto (fun n : ℕ => ((word n).length : ℝ)/(word (n-1)).length) atTop (𝓝 φ) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  have h := Fibonacci.golden_fibonacci_ratio_limits.2.2.comp (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def, length_word, Nat.cast_mul, mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)] using h

noncomputable def frequency (n : ℕ) (s : Option Fibonacci.Letter) : ℝ :=
  ((word n).count s : ℝ) / (word n).length

theorem frequency_formulas (n : ℕ) :
    frequency n none = 1/2 ∧
    frequency n (some .b) = (precedingFib n : ℝ)/(2*fib (n+1)) ∧
    frequency n (some .a) = (fib n : ℝ)/(2*fib (n+1)) := by
  have hp := Fibonacci.fib_positive n
  obtain ⟨h₁,h₂,h₃⟩ := letter_counts n
  simp only [frequency, h₁,h₂,h₃, length_word, Nat.cast_mul, Nat.cast_ofNat]
  exact ⟨by field_simp; ring, trivial, trivial⟩

/-- The ternary letter-density limits obtained by dividing the three
Fibonacci counts by the word length. -/
theorem frequency_limits :
    Tendsto (fun n => frequency n (some .b)) atTop (𝓝 (1/(2*φ^2))) ∧
    Tendsto (fun n => frequency n (some .a)) atTop (𝓝 (1/(2*φ))) := by
  obtain ⟨h₁,h₂,_⟩ := Fibonacci.golden_fibonacci_ratio_limits
  constructor
  · have h : Tendsto (fun n : ℕ => (precedingFib n : ℝ)/fib (n+1)) atTop (𝓝 (φ⁻¹^2)) := by
      apply h₂.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rfl
    convert h.div_const 2 using 1
    · funext n
      rw [(frequency_formulas n).2.1]
      ring
    · congr 1
      have algebra (x : ℝ) (hx : 0 < x) : 1/(2*x^2) = x⁻¹^2/2 := by field_simp; ring
      exact algebra _ gold_pos
  · convert h₁.div_const 2 using 1
    · funext n
      rw [(frequency_formulas n).2.2]
      ring
    · congr 1
      simp [one_div, mul_inv_rev, inv_pow, div_eq_mul_inv, mul_comm]

end Thesis.TernaryWord
