import Thesis.MBonacciCharacteristic
import Thesis.PolynomialRecurrence
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Polynomial.Basic

open Filter Topology Polynomial
open Thesis.Recurrence
open scoped BigOperators

namespace Thesis.MBonacci

/-- The recurrence for prefix lengths quoted from Fischler in
`prop:mbonacci`. The original index is i=k+m, with m=n+2. -/
def PrefixLengthRecurrence (n : Nat) (lengths : Nat → Nat) : Prop :=
  ∀ k > 0, (lengths (k + (n + 2) + 1) : ℝ) =
    2 * lengths (k + (n + 2)) - lengths k

private theorem normalized_prefix_has_coefficient (n : Nat) (p : Nat → Nat)
    (h : PrefixLengthRecurrence n p) :
    ∃ c : ℝ, Tendsto (fun k => (p (k + 1) : ℝ) / beta n ^ k) atTop (𝓝 c) := by
  let d : ℂ := (beta n : ℂ)
  let u : Nat → ℂ := fun k => (p (k + 1) : ℂ) / d ^ k
  have hd : d ≠ 0 := by
    have hpos : 0 < beta n := zero_lt_one.trans (beta_spec n).1
    dsimp only [d]
    exact_mod_cast hpos.ne'
  obtain ⟨q, hq, hm, hqd, hroots⟩ := lengthPolynomial_dominant_factor n
  have hh : ∀ z ∈ q.roots, ‖z‖ < ‖d‖ := by
    intro z hz
    have hpos : 0 ≤ beta n := (zero_lt_one.trans (beta_spec n).1).le
    simpa only [d, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] using hroots z hz
  have hzero : aeval (weightedShift d) (lengthPolynomial (n + 2)) u = 0 := by
    funext k
    have heval (i : Nat) :
        (weightedShift d ^ i) u k = (p (k + i + 1) : ℂ) / d ^ k := by
      rw [weightedShift_pow_apply]
      dsimp only [u]
      rw [pow_add]
      field_simp [hd]
      ring
    have htwo : (2 : ℂ[X]) = C (2 : ℂ) := by
      exact (map_ofNat C 2).symm
    simp only [lengthPolynomial, htwo, map_sub, map_add, map_pow, aeval_X, map_mul, map_one,
      aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.sub_apply, LinearMap.add_apply,
      Module.End.mul_apply, Module.End.one_apply, LinearMap.smul_apply, Pi.smul_apply,
      smul_eq_mul, Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    have hcast : (p (k + 1 + (n + 2) + 1) : ℂ) =
        2 * (p (k + 1 + (n + 2)) : ℂ) - (p (k + 1) : ℂ) := by
      exact_mod_cast h (k + 1) (by omega)
    have hsum₁ : k + (n + 2 + 1) + 1 = k + 1 + (n + 2) + 1 := by omega
    have hsum₂ : k + (n + 2) + 1 = k + 1 + (n + 2) := by omega
    simp only [heval, hsum₁, hsum₂, hcast]
    dsimp only [u]
    ring
  rw [hq] at hzero
  obtain ⟨c, hc⟩ := exists_dominant_coefficient hd hm (IsAlgClosed.splits q) hqd hh hzero
  refine ⟨c.re, ?_⟩
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  convert hr using 1
  ext k
  simp only [Function.comp_apply, u, d]
  norm_cast

private theorem shifted_prefix_gap_recurrence (n : Nat) (p : Nat → Nat)
    (h : PrefixLengthRecurrence n p) (i : Nat) :
    (p (i + (n + 2) + 2) : ℝ) - p (i + (n + 2) + 1) =
      ∑ j ∈ Finset.range (n + 2), ((p (i + j + 2) : ℝ) - p (i + j + 1)) := by
  have he := prefix_gap_recurrence (n + 2) (fun j => (p j : ℝ)) h (i + 1) (by omega)
  have hf (a : Nat) : i + 1 + a + 1 = i + a + 2 := by omega
  have hf' (a : Nat) : i + 1 + a = i + a + 1 := by omega
  convert he using 1
  · rw [hf, hf']
  · apply Finset.sum_congr rfl
    intro j _
    rw [hf, hf']

private theorem prefix_gap_lower_bound (n : Nat) (p : Nat → Nat) (hp : StrictMono p)
    (h : PrefixLengthRecurrence n p) (k : Nat) :
    (beta n ^ (n + 2))⁻¹ * beta n ^ k ≤ (p (k + 2) : ℝ) - p (k + 1) := by
  let m := n + 2
  let b := beta n
  let g : Nat → ℝ := fun i => (p (i + 2) : ℝ) - p (i + 1)
  let δ : ℝ := (b ^ m)⁻¹
  change δ * b ^ k ≤ g k
  have hb : 1 < b := (beta_spec n).1
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hδ : 0 < δ := by positivity
  have hsum : b ^ m = ∑ j ∈ Finset.range m, b ^ j :=
    sub_eq_zero.mp (beta_spec n).2
  have hrec (i : Nat) : g (i + m) = ∑ j ∈ Finset.range m, g (i + j) :=
    shifted_prefix_gap_recurrence n p h i
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < m
    · have hgap : 1 ≤ g k := by
        have hnat : p (k + 1) + 1 ≤ p (k + 2) := hp (by omega)
        have hr : (p (k + 1) : ℝ) + 1 ≤ p (k + 2) := by exact_mod_cast hnat
        dsimp [g]
        linarith
      calc
        δ * b ^ k ≤ δ * b ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb.le hk.le) hδ.le
        _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hb0.ne')
        _ ≤ g k := hgap
    · have hk' : m ≤ k := Nat.le_of_not_gt hk
      let i := k - m
      have hi : i + m = k := Nat.sub_add_cancel hk'
      rw [← hi, hrec, pow_add, hsum, ← mul_assoc, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < m := Finset.mem_range.mp hj
      rw [mul_assoc, ← pow_add]
      exact ih (i + j) (by omega)

/-- The positive gaps between consecutive palindromic prefix lengths
eventually increase and grow without bound, as in `prop:mbonacci`. -/
theorem prefix_gaps_grow (n : Nat) (p : Nat → Nat) (hp : StrictMono p)
    (h : PrefixLengthRecurrence n p) :
    (∀ᶠ k in atTop, (p (k + 2) : ℝ) - p (k + 1) < (p (k + 3) : ℝ) - p (k + 2)) ∧
    Tendsto (fun k => (p (k + 2) : ℝ) - p (k + 1)) atTop atTop := by
  let g : Nat → ℝ := fun i => (p (i + 2) : ℝ) - p (i + 1)
  have hg (j : Nat) : 0 < g j := by
    have hh := hp (show j + 1 < j + 2 by omega)
    exact sub_pos.mpr (by exact_mod_cast hh)
  constructor
  · filter_upwards [eventually_ge_atTop (n + 1)] with k hk
    change g k < g (k + 1)
    let i := k - (n + 1)
    have hi : i + (n + 1) = k := Nat.sub_add_cancel hk
    have hi' : i + (n + 2) = k + 1 := by omega
    have hsum : g (i + (n + 2)) = ∑ j ∈ Finset.range (n + 2), g (i + j) :=
      shifted_prefix_gap_recurrence n p h i
    rw [← hi', hsum, Finset.sum_range_succ, hi]
    apply lt_add_of_pos_left
    apply Finset.sum_pos'
    · exact fun j _ => (hg _).le
    · exact ⟨0, Finset.mem_range.mpr (by omega), hg _⟩
  · have hb : 1 < beta n := (beta_spec n).1
    have hδ : 0 < (beta n ^ (n + 2))⁻¹ := by positivity
    exact tendsto_atTop_mono (prefix_gap_lower_bound n p hp h)
      ((tendsto_pow_atTop_atTop_of_one_lt hb).const_mul_atTop hδ)

private theorem coefficient_positive (n : Nat) (p : Nat → Nat) (hp : StrictMono p)
    (h : PrefixLengthRecurrence n p) {c : ℝ}
    (hc : Tendsto (fun k => (p (k + 1) : ℝ) / beta n ^ k) atTop (𝓝 c)) :
    0 < c := by
  let b := beta n
  let δ : ℝ := (b ^ (n + 2))⁻¹
  have hb : 0 < b := zero_lt_one.trans (beta_spec n).1
  have hδ : 0 < δ := by positivity
  have hl : ∀ᶠ k in atTop, δ / b ≤ (p (k + 1) : ℝ) / b ^ k := by
    filter_upwards [eventually_ge_atTop (1 : Nat)] with k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hgap := prefix_gap_lower_bound n p hp h j
    have hsum : j + 1 + 1 = j + 2 := by omega
    rw [hsum]
    apply (le_div_iff₀ (pow_pos hb _)).2
    have he : δ / b * b ^ (j + 1) = δ * b ^ j := by
      rw [pow_succ]
      field_simp [hb.ne']
      ring
    rw [he]
    exact hgap.trans (sub_le_self _ (Nat.cast_nonneg _))
  exact (div_pos hδ hb).trans_le (ge_of_tendsto hc hl)

/-- The ratio limit in `prop:mbonacci`, from Fischler's cited recurrence.
The positive coefficient of βⁱ follows by comparison of the positive
prefix gaps with the geometric solution of their recurrence. -/
theorem prefix_ratio_tendsto_beta (n : Nat) (p : Nat → Nat) (hp : StrictMono p)
    (hFischler : PrefixLengthRecurrence n p) :
    Tendsto (fun k => (p (k + 1) : ℝ) / (p k : ℝ)) atTop (𝓝 (beta n)) := by
  obtain ⟨c, hc⟩ := normalized_prefix_has_coefficient n p hFischler
  have hpos := coefficient_positive n p hp hFischler hc
  have hd := (zero_lt_one.trans (beta_spec n).1).ne'
  have h := ((hc.comp (tendsto_add_atTop_nat 1)).div hc hpos.ne').const_mul (beta n)
  rw [div_self hpos.ne', mul_one] at h
  apply (tendsto_add_atTop_iff_nat 1).mp
  refine h.congr' (Eventually.of_forall fun k => ?_)
  have hlen : (p (k + 1) : ℝ) ≠ 0 := by
    have hpos' := hp (show 0 < k + 1 by omega)
    exact_mod_cast (show p (k + 1) ≠ 0 by omega)
  simp only [Function.comp_apply, Nat.add_assoc, Nat.reduceAdd, pow_succ]
  field_simp [hd, hlen]
  ring

/-- The conclusion for the indexed palindromic prefix lengths, under
Fischler's length recurrence used in the dissertation. -/
theorem density_of_prefix_recurrence (n : Nat) (p : Nat → Nat) (hp : StrictMono p)
    (hFischler : PrefixLengthRecurrence n p) :
    1 / limsup (fun k => (p (k + 1) : ℝ) / (p k : ℝ)) atTop = 1 / beta n :=
  density_of_prefix_ratio n p (prefix_ratio_tendsto_beta n p hp hFischler)

end Thesis.MBonacci
