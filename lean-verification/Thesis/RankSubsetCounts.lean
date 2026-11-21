import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Positivity

open Finset

namespace Thesis.StudyANCOVA

/-- Count all subsets with weight below a cutoff. The product expands over
the actual powerset, so repeated scores still represent distinct pupils.
The base exceeds the number of subsets. Reduction modulo a power of the
base selects a prefix; reduction modulo base−1 sums its coefficients. -/
theorem encoded_prefix_card {ι : Type*} [DecidableEq ι] (pool : Finset ι) (w : ι → ℕ)
    (B k : ℕ) (hB : pool.powerset.card < B-1) :
    (((∏ i ∈ pool, (1+B^(w i))) % B^(k+1)) % (B-1)) =
      (pool.powerset.filter fun s => ∑ i ∈ s, w i ≤ k).card := by
  classical
  let code := fun s : Finset ι => ∑ i ∈ s, w i
  let all := pool.powerset
  let lo := all.filter fun s => code s ≤ k
  let hi := all.filter fun s => ¬code s ≤ k
  have base : 1 < B := by omega
  have ca : lo.card < B-1 := (card_filter_le _ _).trans_lt hB
  have expand : ∏ i ∈ pool, (1+B^(w i)) = (∑ s ∈ lo, B^(code s)) + ∑ s ∈ hi, B^(code s) := by
    rw [prod_one_add]
    simp only [prod_pow_eq_pow_sum]
    exact (sum_filter_add_sum_filter_not all (fun s => code s ≤ k) _).symm
  have small : ∑ s ∈ lo, B^(code s) < B^(k+1) := by
    calc
      _ ≤ ∑ _s ∈ lo, B^k := sum_le_sum (fun s hs => Nat.pow_le_pow_right (by omega) (mem_filter.1 hs).2)
      _ = lo.card*B^k := by simp
      _ < B^(k+1) := by rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  have divs : B^(k+1) ∣ ∑ s ∈ hi, B^(code s) :=
    dvd_sum (fun s hs => pow_dvd_pow B (show k+1 ≤ code s from by have := (mem_filter.1 hs).2; omega))
  have mod1 : B ≡ 1 [MOD (B-1)] :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ B)).2 (dvd_refl _) |>.symm
  have lowmod : (∑ s ∈ lo, B^(code s)) % (B-1) = lo.card := by
    rw [sum_nat_mod]
    have one (s : Finset ι) : B^code s % (B-1) = 1%(B-1) := by
      simpa using (mod1.pow (code s))
    simp only [one]
    by_cases hc : 1 < B-1
    · simp [Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt ca]
    · have z : lo.card = 0 := by omega
      simp [z]
  rw [expand,Nat.add_mod,Nat.mod_eq_zero_of_dvd divs,add_zero,Nat.mod_mod,Nat.mod_eq_of_lt small]
  exact lowmod

end Thesis.StudyANCOVA

