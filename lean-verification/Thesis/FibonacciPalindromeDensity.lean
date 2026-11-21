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

/-- Between two known central lengths, the next palindromic prefix
cannot come later than the next central prefix. This uses only the
central prefixes constructed in `lem:palFib`. -/
theorem inverse_prefix_ratio_ge_central {u v k : Nat}
    (huv : ConsecutivePalPrefixes infiniteWord u v)
    (hlo : fib (k + 3) - 2 ≤ u) (hhi : u < fib (k + 4) - 2) :
    ((fib (k + 3) - 2 : Nat) : ℝ) / ((fib (k + 4) - 2 : Nat) : ℝ) ≤
      (u : ℝ) / v := by
  have hnext := central_palPrefix (k + 1)
  change PalPrefix infiniteWord (fib (k + 4) - 2) at hnext
  have hv : v ≤ fib (k + 4) - 2 := by
    by_contra! hv
    exact huv.2.2.2.2 _ hhi hv hnext
  exact div_le_div_of_nonneg_left (by positivity)
    (by exact_mod_cast (huv.1.trans huv.2.1))
    (by exact_mod_cast hv) |>.trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (by positivity))

/-- The eventual lower bound on inverse ratios in the direct half of
`thm:palFib`, obtained by bracketing a length between central lengths. -/
theorem eventually_inverse_prefix_ratios_ge {c : ℝ} (hc : c < 1 / φ) :
    ∃ K : Nat, ∀ u v, K ≤ u → ConsecutivePalPrefixes infiniteWord u v → c ≤ (u : ℝ) / v := by
  let a := fun k : Nat => fib (k + 3) - 2
  have hlt := central_inverse_ratios_tendsto.eventually (lt_mem_nhds hc)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlt
  refine ⟨a N, fun u v hu huv => ?_⟩
  have hgt : ∃ j, u < a j := by
    obtain ⟨j, hj⟩ := (central_length_strictMono.tendsto_atTop.eventually
      (eventually_gt_atTop u)).exists
    exact ⟨j, hj⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (n := Nat.find hgt) (by
    intro he
    have h := Nat.find_spec hgt
    rw [he] at h
    have h0 : a 0 = 0 := by decide
    omega)
  have hlo : a k ≤ u := by
    have hmin := Nat.find_min hgt (m := k) (by omega)
    omega
  have hhi : u < a (k + 1) := by simpa only [hk] using Nat.find_spec hgt
  have hkN : N ≤ k := by
    by_contra! hn
    exact (not_lt_of_ge hu) (hhi.trans_le (central_length_strictMono.monotone (by omega : k + 1 ≤ N)))
  exact (hN k hkN).le.trans (inverse_prefix_ratio_ge_central huv hlo hhi)

/-- The lower bound on density proved directly in `thm:palFib`. -/
theorem one_div_gold_le_palindromicDensity : 1 / φ ≤ palindromicDensity infiniteWord := by
  apply le_palindromicDensity_of_late_inverse_ratios
  · exact (Set.infinite_range_of_injective central_length_strictMono.injective).mono
      (by rintro _ ⟨k, rfl⟩; exact central_palPrefix k)
  · exact fun _ => eventually_inverse_prefix_ratios_ge

/-- The density in `thm:palFib`. The reverse inequality uses the complete
prefix list stated in the preceding remark. -/
theorem infiniteWord_palindromicDensity : palindromicDensity infiniteWord = 1 / φ := by
  refine le_antisymm ?_ one_div_gold_le_palindromicDensity
  exact (palindromicDensity_eq_of_cut (by positivity) fun _ _ hq =>
    belowPalDensity_iff_of_ratio_limit central_length_strictMono infiniteWord_palPrefix_iff
      central_inverse_ratios_tendsto hq).le

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
