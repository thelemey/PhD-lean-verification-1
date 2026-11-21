import Thesis.FibonacciCompletePrefixes
import Thesis.PalindromicDensityReal
import Thesis.TernaryRichness

open Filter Topology
open scoped goldenRatio

namespace Thesis.Fibonacci

private theorem central_length_strictMono : StrictMono (fun n => fib (n + 3) - 2) := by
  convert MBonacci.palindromePrefixLengths_strictMono 0 using 1
  funext n
  rw [binary_closure_lengths, central_length]

private theorem central_inverse_ratios_tendsto :
    Tendsto (fun n : Nat => ((fib (n + 3) - 2 : Nat) : ℝ) / ((fib (n + 4) - 2 : Nat) : ℝ))
      atTop (𝓝 (1 / φ)) := by
  have hratio : Tendsto (fun n : Nat => (fib (n + 3) : ℝ) / fib (n + 4))
      atTop (𝓝 (1 / φ)) :=
    golden_fibonacci_ratio_limits.1.comp (tendsto_add_atTop_nat 3)
  have hf : Tendsto (fun n : Nat => fib (n + 4)) atTop atTop := by
    have hf' := central_length_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
    exact tendsto_atTop_mono (fun n => Nat.sub_le (fib (n + 4)) 2) hf'
  have hsmall : Tendsto (fun n : Nat => (2 : ℝ) / fib (n + 4)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 2).comp hf
  have h := (hratio.sub hsmall).div (tendsto_const_nhds.sub hsmall :
    Tendsto (fun n : Nat => (1 : ℝ) - 2 / fib (n + 4)) atTop (𝓝 (1 - 0))) (by norm_num)
  rw [sub_zero, sub_zero, div_one] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  have h₃ : 2 ≤ fib (n + 3) := fib_at_least_two n
  have h₄ : 2 < fib (n + 4) := by
    change 2 < fib (n + 2) + fib (n + 3)
    have : 0 < fib (n + 2) := fib_positive (n + 1)
    omega
  have h₄R : (2 : ℝ) < fib (n + 4) := by exact_mod_cast h₄
  change (((fib (n + 3) : ℝ) / fib (n + 4) - 2 / fib (n + 4)) /
    (1 - 2 / fib (n + 4))) =
      ((fib (n + 3) - 2 : Nat) : ℝ) / ((fib (n + 4) - 2 : Nat) : ℝ)
  rw [Nat.cast_sub h₃, Nat.cast_sub h₄.le]
  push_cast
  have hp : (fib (n + 4) : ℝ) ≠ 0 := by positivity
  have hp' : (fib (n + 4) : ℝ) - 2 ≠ 0 := (sub_pos.2 h₄R).ne'
  field_simp [hp, hp']

/-- The density in thm:palFib, from the complete central-prefix list and
the limiting ratios of its consecutive lengths. -/
theorem infiniteWord_palindromicDensity : palindromicDensity infiniteWord = 1 / φ :=
  palindromicDensity_eq_of_cut (by positivity) fun _ _ hq =>
    belowPalDensity_iff_of_ratio_limit central_length_strictMono infiniteWord_palPrefix_iff
      central_inverse_ratios_tendsto hq

end Thesis.Fibonacci

namespace Thesis.TernaryWord

/-- The full list in thm:Ypal, obtained by the separator correspondence. -/
theorem ternary_palPrefix_iff {L : Nat} (hL : 0 < L) :
    PalPrefix infiniteWord L ↔ ∃ n, 2 * Fibonacci.fib (n + 3) - 3 = L := by
  rw [infiniteWord_eq_insertSeparator, palPrefix_insert_iff _ hL]
  constructor
  · rintro ⟨m, he, hp⟩
    obtain ⟨n, hn⟩ := (Fibonacci.infiniteWord_palPrefix_iff m).1 hp
    have hb := Fibonacci.fib_at_least_two n
    exact ⟨n, by omega⟩
  · rintro ⟨n, hn⟩
    have hb := Fibonacci.fib_at_least_two n
    exact ⟨Fibonacci.fib (n + 3) - 2, by omega,
      (Fibonacci.infiniteWord_palPrefix_iff _).2 ⟨n, rfl⟩⟩

/-- The second proof in thm:Ypal, using the invariance under insertion. -/
theorem ternary_palindromicDensity : palindromicDensity infiniteWord = 1 / φ := by
  rw [infiniteWord_eq_insertSeparator, palindromicDensity_insert,
    Fibonacci.infiniteWord_palindromicDensity]

end Thesis.TernaryWord
