import Thesis.RecurrenceStability
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Pi

open Filter Topology Polynomial
open scoped BigOperators

namespace Thesis.Recurrence

/-- On a sequence already divided by the nth power of d, the original
shift acts as the shift multiplied by d. -/
noncomputable def weightedShift (d : ℂ) : Module.End ℂ (Nat → ℂ) where
  toFun u n := d * u (n + 1)
  map_add' u v := by ext n; exact mul_add _ _ _
  map_smul' c u := by ext n; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp]
theorem weightedShift_apply (d : ℂ) (u : Nat → ℂ) (n : Nat) :
    weightedShift d u n = d * u (n + 1) := rfl

theorem weightedShift_pow_apply (d : ℂ) (k : Nat) (u : Nat → ℂ) (n : Nat) :
    (weightedShift d ^ k) u n = d ^ k * u (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, weightedShift_apply, ih, pow_succ']
    rw [mul_assoc, show n + 1 + k = n + (k + 1) by omega]

private theorem factor_apply (d z : ℂ) (u : Nat → ℂ) (n : Nat) :
    aeval (weightedShift d) (X - C z) u n = d * u (n + 1) - z * u n := by
  simp [Algebra.algebraMap_eq_smul_one, smul_eq_mul]

private theorem aeval_constant (d c : ℂ) (p : ℂ[X]) :
    aeval (weightedShift d) p (fun _ => c) = fun _ => p.eval d * c := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, hp, hq, eval_add]
    ext n
    exact (add_mul _ _ _).symm
  | monomial k a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, aeval_C]
    ext n
    simp [Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, weightedShift_pow_apply,
      eval_monomial, mul_assoc, smul_eq_mul]

private theorem tendsto_zero_of_split_factors {d : ℂ} (hd : d ≠ 0)
    {roots : Multiset ℂ} (hroots : ∀ z ∈ roots, ‖z‖ < ‖d‖)
    {u : Nat → ℂ}
    (h : Tendsto (aeval (weightedShift d) (roots.map fun z => X - C z).prod u)
      atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  induction roots using Multiset.induction_on generalizing u with
  | empty => simpa using h
  | cons z roots ih =>
    have hz : ‖z‖ < ‖d‖ := hroots z (Multiset.mem_cons_self _ _)
    have ht : ∀ r ∈ roots, ‖r‖ < ‖d‖ :=
      fun r hr => hroots r (Multiset.mem_cons_of_mem hr)
    have he : (X - C z) * (roots.map (fun r => X - C r)).prod =
        (roots.map (fun r => X - C r)).prod * (X - C z) := mul_comm _ _
    rw [Multiset.map_cons, Multiset.prod_cons, he, map_mul, Module.End.mul_apply] at h
    have h₁ := ih ht h
    have h₂ : Tendsto (fun n => d * u (n + 1) - z * u n) atTop (𝓝 0) := by
      convert h₁ using 1
      ext n
      exact (factor_apply d z u n).symm
    have h₃ := h₂.const_mul d⁻¹
    rw [mul_zero] at h₃
    apply tendsto_zero_of_difference (z := z / d)
    · rwa [norm_div, div_lt_one (norm_pos_iff.2 hd)]
    · refine h₃.congr fun n => ?_
      field_simp [hd]
      ring

private theorem tendsto_zero_of_small_roots {d : ℂ} (hd : d ≠ 0)
    {p : ℂ[X]} (hp : p.Monic) (hsplit : p.Splits (RingHom.id ℂ))
    (hsmall : ∀ z ∈ p.roots, ‖z‖ < ‖d‖) {u : Nat → ℂ}
    (h : Tendsto (aeval (weightedShift d) p u) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) :=
  tendsto_zero_of_split_factors hd hsmall
    ((eq_prod_roots_of_monic_of_splits_id hp hsplit) ▸ h)

/-- The coefficient of the dominant geometric term in a recurrence solution.
The input is the solution divided by dⁿ, so its limit is that coefficient.
The factor X-d occurs once and all roots of the remaining monic factor
have smaller norm. -/
theorem exists_dominant_coefficient {d : ℂ} (hd : d ≠ 0) {q : ℂ[X]} (hq : q.Monic)
    (hqs : q.Splits (RingHom.id ℂ)) (hq_d : q.eval d ≠ 0) (hsmall : ∀ z ∈ q.roots, ‖z‖ < ‖d‖) {u : Nat → ℂ}
    (hu : aeval (weightedShift d) ((X - C d) * q) u = 0) :
    ∃ c : ℂ, Tendsto u atTop (𝓝 c) := by
  let v := aeval (weightedShift d) q u
  have hstep (n : Nat) : v (n + 1) = v n := by
    have h := congrFun hu n
    rw [map_mul, Module.End.mul_apply, factor_apply] at h
    change d * v (n + 1) - d * v n = 0 at h
    exact mul_left_cancel₀ hd (sub_eq_zero.1 h)
  have hconst (n : Nat) : v n = v 0 := by
    induction n with
    | zero => rfl
    | succ n ih => exact (hstep n).trans ih
  let c := v 0 / q.eval d
  let w : Nat → ℂ := fun _ => c
  have hv : aeval (weightedShift d) q (u - w) = 0 := by
    rw [LinearMap.map_sub, aeval_constant]
    ext n
    change v n - q.eval d * c = 0
    rw [hconst, mul_comm, div_mul_cancel₀ _ hq_d, sub_self]
  have hz := tendsto_zero_of_small_roots hd hq hqs hsmall
    (show Tendsto (aeval (weightedShift d) q (u - w)) atTop (𝓝 0) by
      rw [hv]
      exact tendsto_const_nhds)
  refine ⟨c, ?_⟩
  exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa using hz.norm)

end Thesis.Recurrence
