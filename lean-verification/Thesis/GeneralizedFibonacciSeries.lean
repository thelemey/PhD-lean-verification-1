import Thesis.Fibonacci
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace Thesis.Fibonacci

/-- The recurrence of the corrected definition, with order `r`. -/
def generalizedTerm (t p r n : Nat) : Nat :=
  if n < r ∨ n = 0 then
    if n = r - 1 then 1 else 0
  else
    t * generalizedTerm t p r (n - 1) +
      ∑ j ∈ (Finset.Icc (p + 1) r).attach,
        generalizedTerm t p r (n - j.val)
termination_by n
decreasing_by
  · have : 0 < n := by omega
    omega
  · have hj := (Finset.mem_Icc.1 j.property).1
    omega

private theorem generalizedTerm_initial {t p r n : Nat} (hn : n < r) :
    generalizedTerm t p r n = if n = r - 1 then 1 else 0 := by
  rw [generalizedTerm, if_pos (Or.inl hn)]

private theorem generalizedTerm_recur {t p r n : Nat} (hr : 2 ≤ r) (hn : r ≤ n) :
    generalizedTerm t p r n = t * generalizedTerm t p r (n - 1) +
      ∑ j ∈ Finset.Icc (p + 1) r, generalizedTerm t p r (n - j) := by
  rw [generalizedTerm, if_neg (by omega)]
  apply congrArg (fun s : Nat => t * generalizedTerm t p r (n - 1) + s)
  exact Finset.sum_attach _ (fun j : Nat => generalizedTerm t p r (n - j))

def GeneralizedFibSpec (t p r : Nat) (f : Nat → Nat) : Prop :=
  (∀ n < r - 1, f n = 0) ∧ f (r - 1) = 1 ∧
    ∀ n ≥ r, f n = t * f (n - 1) + ∑ j ∈ Finset.Icc (p + 1) r, f (n - j)

theorem generalizedTerm_spec (t p r : Nat) (hr : 2 ≤ r) :
    GeneralizedFibSpec t p r (generalizedTerm t p r) := by
  refine ⟨?_, ?_, fun n hn => generalizedTerm_recur hr hn⟩
  · intro n hn
    rw [generalizedTerm_initial (by omega), if_neg (by omega)]
  · rw [generalizedTerm_initial (by omega), if_pos rfl]

/-- Existence and uniqueness for the corrected initial conditions. -/
theorem generalizedFib_existsUnique (t k p : Nat) (hk : 2 ≤ k) (hp : 1 ≤ p) :
    ∃! f, GeneralizedFibSpec t p (k + p - 1) f := by
  let r := k + p - 1
  change ∃! f, GeneralizedFibSpec t p r f
  have hr : 2 ≤ r := by dsimp [r]; omega
  refine ⟨generalizedTerm t p r, generalizedTerm_spec t p r hr, ?_⟩
  intro f ⟨hzero, hone, hrec⟩
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < r
    · rw [generalizedTerm_initial hn]
      split
      · rename_i he
        simpa only [he] using hone
      · exact hzero n (by omega)
    · rw [hrec n (by omega), generalizedTerm_recur hr (by omega), ih (n - 1) (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hlo := (Finset.mem_Icc.1 hj).1
      exact ih (n - j) (by omega)

open PowerSeries

def generalizedSeries (f : Nat → Nat) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (f n : ℚ)

noncomputable def generalizedDenominator (t p r : Nat) : PowerSeries ℚ :=
  1 - C ℚ (t : ℚ) * X - ∑ j ∈ Finset.Icc (p + 1) r, (X : PowerSeries ℚ) ^ j

/-- Coefficient multiplication as in the proof of `lemgenn1`. -/
theorem generalizedSeries_mul_denominator {t p r : Nat} (hr : 2 ≤ r) {f : Nat → Nat}
    (hs : GeneralizedFibSpec t p r f) :
    generalizedDenominator t p r * generalizedSeries f = (X : PowerSeries ℚ) ^ (r - 1) := by
  obtain ⟨hzero, hone, hrec⟩ := hs
  ext n
  have ht : coeff ℚ n ((C ℚ (t : ℚ) * X) * generalizedSeries f) =
      (t : ℚ) * (if 1 ≤ n then (f (n - 1) : ℚ) else 0) := by
    rw [mul_assoc, coeff_C_mul, show X * generalizedSeries f =
      (X : PowerSeries ℚ) ^ 1 * generalizedSeries f by simp, coeff_X_pow_mul']
    simp only [generalizedSeries, coeff_mk]
  unfold generalizedSeries at ht
  simp only [generalizedDenominator, sub_mul, one_mul, map_sub, ht, Finset.sum_mul, map_sum,
    coeff_X_pow_mul', generalizedSeries, coeff_mk, coeff_X_pow]
  by_cases hn : n < r
  · have hz₁ : (if 1 ≤ n then (f (n - 1) : ℚ) else 0) = 0 := by
      split
      · rw [hzero _ (by omega), Nat.cast_zero]
      · rfl
    have hz₂ : (∑ j ∈ Finset.Icc (p + 1) r, if j ≤ n then (f (n - j) : ℚ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjpos := (Finset.mem_Icc.1 hj).1
      split
      · rw [hzero _ (by omega), Nat.cast_zero]
      · rfl
    rw [hz₁, mul_zero, sub_zero, hz₂, sub_zero]
    by_cases he : n = r - 1
    · simp [he, hone]
    · simp [he, hzero _ (by omega : n < r - 1)]
  · have hle : r ≤ n := by omega
    rw [if_pos (by omega : 1 ≤ n), if_neg (by omega : n ≠ r - 1)]
    have hsum :
        (∑ j ∈ Finset.Icc (p + 1) r, if j ≤ n then (f (n - j) : ℚ) else 0) =
          ∑ j ∈ Finset.Icc (p + 1) r, (f (n - j) : ℚ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos ((Finset.mem_Icc.1 hj).2.trans hle)]
    rw [hsum]
    have h := congrArg (fun m : Nat => (m : ℚ)) (hrec n hle)
    push_cast at h
    rw [h]
    ring

/-- Multiplying by the inverse of the series with constant coefficient one
gives the formal generating function in the corrected dissertation. -/
theorem generalizedSeries_closed_form {t p r : Nat} (hr : 2 ≤ r) {f : Nat → Nat}
    (hs : GeneralizedFibSpec t p r f) :
    generalizedSeries f = (X : PowerSeries ℚ) ^ (r - 1) * (generalizedDenominator t p r)⁻¹ := by
  have hsum : (∑ j ∈ Finset.Icc (p + 1) r, (0 : ℚ) ^ j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact zero_pow (by have := (Finset.mem_Icc.1 hj).1; omega)
  have hD : constantCoeff ℚ (generalizedDenominator t p r) ≠ 0 := by
    simp [generalizedDenominator, map_sum, hsum]
  calc
    generalizedSeries f =
        (generalizedDenominator t p r)⁻¹ * (generalizedDenominator t p r * generalizedSeries f) := by
      rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hD, one_mul]
    _ = _ := by rw [generalizedSeries_mul_denominator hr hs, mul_comm]

theorem generalizedTerm_generating_function (t k p : Nat) (hk : 2 ≤ k) (hp : 1 ≤ p) :
    let r := k + p - 1
    generalizedSeries (generalizedTerm t p r) =
      (X : PowerSeries ℚ) ^ (r - 1) * (generalizedDenominator t p r)⁻¹ := by
  have hr : 2 ≤ k + p - 1 := by omega
  exact generalizedSeries_closed_form hr (generalizedTerm_spec t p _ hr)

theorem generalizedSeries_p_one {t k : Nat} (hk : 2 ≤ k) {f : Nat → Nat}
    (hs : GeneralizedFibSpec t 1 k f) :
    generalizedSeries f =
      (X : PowerSeries ℚ) ^ (k - 1) *
        (1 - C ℚ (t : ℚ) * X - ∑ j ∈ Finset.Icc 2 k, (X : PowerSeries ℚ) ^ j)⁻¹ := by
  exact generalizedSeries_closed_form hk hs

end Thesis.Fibonacci
