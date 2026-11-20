import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.ModEq
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

open Filter Topology Set
open scoped BigOperators

namespace Thesis.MBonacci

/-- The directive word (a₁…aₘ) repeated, with the letters and positions
indexed from zero. -/
def directive (m n : Nat) : Nat := n % m

/-- Before the end of the first period, the directive letter is new. -/
theorem directive_first_occurrence {m n : Nat} (hn : n < m) :
    ∀ i < n, directive m i ≠ directive m n := by
  intro i hi
  simp only [directive, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (hi.trans hn)]
  exact hi.ne

/-- After the first period, the previous occurrence is at n-m. This is
the directive-word computation used for ψ in `prop:mbonacci`. -/
theorem directive_previous_occurrence {m n : Nat} (hm : 0 < m) (hn : m ≤ n) :
    n - m < n ∧ directive m (n - m) = directive m n ∧
      ∀ i, n - m < i → i < n → directive m i ≠ directive m n := by
  refine ⟨by omega, ?_, ?_⟩
  · unfold directive
    have he : n - m + m = n := Nat.sub_add_cancel hn
    conv_rhs => rw [← he, Nat.add_mod_right]
  · intro i hi hin he
    have hdvd : m ∣ n - i := (Nat.modEq_iff_dvd' hin.le).mp he
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hin) hdvd
    omega

/-- The recurrence for prefix lengths quoted in `prop:mbonacci`
gives the m-step sum recurrence for their successive differences. -/
theorem prefix_gap_recurrence (m : Nat) (prefixLength : Nat → ℝ)
    (hFischler : ∀ k > 0, prefixLength (k + m + 1) =
      2 * prefixLength (k + m) - prefixLength k) (k : Nat) (hk : 0 < k) :
    prefixLength (k + m + 1) - prefixLength (k + m) =
      ∑ j ∈ Finset.range m, (prefixLength (k + j + 1) - prefixLength (k + j)) := by
  calc
    _ = prefixLength (k + m) - prefixLength k := by linarith only [hFischler k hk]
    _ = _ := by
      simpa only [Nat.add_zero, Nat.add_assoc] using
        (Finset.sum_range_sub (fun j => prefixLength (k + j)) m).symm

/-- The characteristic polynomial after removing the factor (x-1)
in the proof of `prop:mbonacci`. -/
def characteristic (m : Nat) (x : ℝ) : ℝ :=
  x ^ m - ∑ j ∈ Finset.range m, x ^ j

theorem characteristic_factor (m : Nat) (x : ℝ) :
    x ^ (m + 1) - 2 * x ^ m + 1 = (x - 1) * characteristic m x := by
  unfold characteristic
  rw [mul_sub, mul_geom_sum, pow_succ]
  ring

private noncomputable def reciprocalSum (m : Nat) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, x⁻¹ ^ (j + 1)

private theorem reciprocalSum_anti {m : Nat} (hm : 0 < m) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) : reciprocalSum m y < reciprocalSum m x := by
  have h : y⁻¹ < x⁻¹ := by
    simpa only [one_div] using one_div_lt_one_div_of_lt hx hxy
  have hy : 0 ≤ y⁻¹ := inv_nonneg.mpr (hx.trans hxy).le
  apply Finset.sum_lt_sum
  · intro j _
    exact pow_le_pow_left₀ hy h.le _
  · refine ⟨0, Finset.mem_range.mpr hm, ?_⟩
    simpa using h

private theorem characteristic_eq_zero_iff {m : Nat} {x : ℝ} (hx : 1 < x) :
    characteristic m x = 0 ↔ reciprocalSum m x = 1 := by
  have hpos : 0 < x := zero_lt_one.trans hx
  have hne : x - 1 ≠ 0 := sub_ne_zero.mpr hx.ne'
  have hsum : reciprocalSum m x = x⁻¹ * (∑ j ∈ Finset.range m, (x⁻¹) ^ j) := by
    unfold reciprocalSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ, mul_comm]
  have hmul : (x - 1) * reciprocalSum m x = 1 - (x⁻¹) ^ m := by
    rw [hsum, ← mul_assoc]
    have he : (x - 1) * x⁻¹ = -(x⁻¹ - 1) := by
      field_simp [hpos.ne']
    rw [he, neg_mul, mul_geom_sum]
    ring
  have hfactor := characteristic_factor m x
  rw [pow_succ] at hfactor
  have hxpow : x ^ m ≠ 0 := pow_ne_zero _ hpos.ne'
  constructor
  · intro hz
    rw [hz, mul_zero] at hfactor
    have hgap : 2 - x = (x⁻¹) ^ m := by
      rw [inv_pow, ← one_div, eq_div_iff hxpow]
      nlinarith only [hfactor]
    have he : (x - 1) * reciprocalSum m x = (x - 1) * 1 := by
      rw [hmul, ← hgap]
      ring
    exact mul_left_cancel₀ hne he
  · intro hs
    rw [hs, mul_one] at hmul
    have hgap : (2 - x) * x ^ m = 1 := by
      have he : 2 - x = (x⁻¹) ^ m := by linarith only [hmul]
      rw [he, inv_pow, inv_mul_cancel₀ hxpow]
    have ht : (x - 1) * characteristic m x = (x - 1) * 0 := by
      nlinarith only [hgap, hfactor]
    exact mul_left_cancel₀ hne ht

/-- The characteristic polynomial has a unique root greater than one.
The proof uses the strictly decreasing normalized geometric sum. -/
theorem existsUnique_root (m : Nat) (hm : 2 ≤ m) :
    ∃! x : ℝ, 1 < x ∧ characteristic m x = 0 := by
  have h1 : characteristic m 1 < 0 := by
    have hcast : (2 : ℝ) ≤ m := by exact_mod_cast hm
    simpa [characteristic] using (show 1 - (m : ℝ) < 0 by linarith)
  have h2 : characteristic m 2 = 1 := by
    have h := characteristic_factor m (2 : ℝ)
    rw [pow_succ] at h
    linarith
  have hc : Continuous (characteristic m) := by
    unfold characteristic
    fun_prop
  obtain ⟨x, hx, hzero⟩ :=
    intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num) hc.continuousOn
      (show (0 : ℝ) ∈ Icc (characteristic m 1) (characteristic m 2) by rw [h2]; exact ⟨h1.le, zero_le_one⟩)
  have hx1 : 1 < x := lt_of_le_of_ne hx.1 (by
    intro he
    subst x
    exact h1.ne hzero)
  refine ⟨x, ⟨hx1, hzero⟩, ?_⟩
  rintro y ⟨hy, hzero'⟩
  have hm' : 0 < m := by omega
  have hs := (characteristic_eq_zero_iff hx1).1 hzero
  have hs' := (characteristic_eq_zero_iff hy).1 hzero'
  rcases lt_trichotomy y x with hlt | he | hgt
  · have h := reciprocalSum_anti hm' (zero_lt_one.trans hy) hlt
    linarith
  · exact he
  · have h := reciprocalSum_anti hm' (zero_lt_one.trans hx1) hgt
    linarith

/-- `beta n` is the root βₘ for m=n+2. -/
noncomputable def beta (n : Nat) : ℝ :=
  (existsUnique_root (n + 2) (by omega)).exists.choose

theorem beta_spec (n : Nat) : 1 < beta n ∧ characteristic (n + 2) (beta n) = 0 :=
  (existsUnique_root (n + 2) (by omega)).exists.choose_spec

private theorem normalized_beta (n : Nat) : reciprocalSum (n + 2) (beta n) = 1 :=
  (characteristic_eq_zero_iff (beta_spec n).1).1 (beta_spec n).2

private theorem beta_step (n : Nat) : beta n < beta (n + 1) := by
  have hpos : 0 < beta n := zero_lt_one.trans (beta_spec n).1
  have hnext : 1 < reciprocalSum (n + 1 + 2) (beta n) := by
    rw [show n + 1 + 2 = n + 2 + 1 by omega, reciprocalSum, Finset.sum_range_succ]
    change 1 < reciprocalSum (n + 2) (beta n) + (beta n)⁻¹ ^ (n + 2 + 1)
    rw [normalized_beta]
    exact lt_add_of_pos_right _ (by positivity)
  by_contra! hle
  rcases lt_or_eq_of_le hle with hlt | he
  · have h := reciprocalSum_anti (m := n + 1 + 2) (by omega)
      (zero_lt_one.trans (beta_spec (n + 1)).1) hlt
    rw [normalized_beta (n + 1)] at h
    linarith
  · have h := normalized_beta (n + 1)
    rw [he] at h
    linarith

theorem beta_strictMono : StrictMono beta :=
  strictMono_nat_of_lt_succ beta_step

private theorem beta_gap (n : Nat) : 2 - beta n = (beta n)⁻¹ ^ (n + 2) := by
  have hb : 0 < beta n := zero_lt_one.trans (beta_spec n).1
  have h := characteristic_factor (n + 2) (beta n)
  rw [(beta_spec n).2, mul_zero, pow_succ] at h
  rw [inv_pow, ← one_div, eq_div_iff (pow_ne_zero _ hb.ne')]
  nlinarith only [h]

/-- The limit of the characteristic roots stated in `prop:mbonacci`. -/
theorem beta_tendsto_two : Tendsto beta atTop (𝓝 2) := by
  have hpos : 0 < beta 0 := zero_lt_one.trans (beta_spec 0).1
  have hlt : (beta 0)⁻¹ < 1 := by
    simpa only [one_div, inv_one] using one_div_lt_one_div_of_lt zero_lt_one (beta_spec 0).1
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hpos.le) hlt).comp
    (tendsto_add_atTop_nat 2)
  have hgap : Tendsto (fun n => 2 - beta n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ?_) (fun n => ?_) hlim
    · rw [beta_gap]
      have := (beta_spec n).1
      positivity
    · rw [beta_gap]
      exact pow_le_pow_left₀ (inv_nonneg.mpr (zero_lt_one.trans (beta_spec n).1).le)
        (by simpa only [one_div] using
          one_div_le_one_div_of_le hpos (beta_strictMono.monotone (Nat.zero_le n))) _
  have h := hgap.const_sub (2 : ℝ)
  simpa using h

/-- The reciprocal roots in `prop:mbonacci` decrease to one half. -/
theorem reciprocal_beta_tendsto_half :
    Tendsto (fun n => 1 / beta n) atTop (𝓝 ((1 : ℝ) / 2)) := by
  simpa only [one_div] using beta_tendsto_two.inv₀ (by norm_num)

theorem reciprocal_beta_strictAnti : StrictAnti (fun n => 1 / beta n) := by
  intro i j hij
  exact one_div_lt_one_div_of_lt (zero_lt_one.trans (beta_spec i).1) (beta_strictMono hij)

private theorem complex_reciprocal_sum {m : Nat} {z : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1)
    (hroot : z ^ m = ∑ j ∈ Finset.range m, z ^ j) :
    (∑ j ∈ Finset.range m, z⁻¹ ^ (j + 1)) = 1 := by
  have hpoly := congrArg (fun w => (z - 1) * w) hroot
  change (z - 1) * z ^ m = (z - 1) * ∑ j ∈ Finset.range m, z ^ j at hpoly
  rw [mul_geom_sum] at hpoly
  have hgap : 2 - z = (z ^ m)⁻¹ := by
    rw [← one_div, eq_div_iff (pow_ne_zero _ hz)]
    linear_combination -hpoly
  apply mul_left_cancel₀ (sub_ne_zero.mpr hz1)
  rw [mul_one, Finset.mul_sum]
  have hcoeff : ∀ j ∈ Finset.range m, (z - 1) * z⁻¹ ^ (j + 1) =
      -(z⁻¹ - 1) * z⁻¹ ^ j := by
    intro j _
    have h : (z - 1) * z⁻¹ = -(z⁻¹ - 1) := by field_simp [hz]
    calc
      _ = ((z - 1) * z⁻¹) * z⁻¹ ^ j := by rw [pow_succ]; ring
      _ = _ := by rw [h]
  rw [Finset.sum_congr rfl hcoeff, ← Finset.mul_sum, neg_mul, mul_geom_sum, inv_pow, ← hgap]
  ring

/-- The positive root in `prop:mbonacci` strictly dominates every other
characteristic root in modulus. -/
theorem other_characteristic_roots_smaller (n : Nat) (z : ℂ)
    (hroot : z ^ (n + 2) = ∑ j ∈ Finset.range (n + 2), z ^ j)
    (hne : z ≠ (beta n : ℂ)) : ‖z‖ < beta n := by
  classical
  by_contra! hle
  have hb := (beta_spec n).1
  have hp : 0 < ‖z‖ := (zero_lt_one.trans hb).trans_le hle
  have hz : z ≠ 0 := norm_pos_iff.1 hp
  have hz1 : z ≠ 1 := by
    intro he
    rw [he, norm_one] at hle
    exact (not_le_of_gt hb) hle
  have hsum := complex_reciprocal_sum hz hz1 hroot
  have hre := congrArg Complex.re hsum
  rw [Complex.re_sum, Complex.one_re] at hre
  have hterm (j : Nat) : (z⁻¹ ^ (j + 1)).re ≤ ‖z‖⁻¹ ^ (j + 1) := by
    simpa only [norm_pow, norm_inv] using Complex.re_le_norm (z⁻¹ ^ (j + 1))
  have htotal : 1 ≤ reciprocalSum (n + 2) ‖z‖ := by
    rw [← hre]
    exact Finset.sum_le_sum fun j _ => hterm j
  have he : ‖z‖ = beta n := by
    rcases lt_or_eq_of_le hle with hlt | he
    · have h := reciprocalSum_anti (m := n + 2) (by omega) (zero_lt_one.trans hb) hlt
      rw [normalized_beta] at h
      linarith
    · exact he.symm
  have hfirst : (z⁻¹).re = ‖z⁻¹‖ := by
    apply le_antisymm (Complex.re_le_norm _)
    by_contra! hlt
    have hs : (∑ j ∈ Finset.range (n + 2), (z⁻¹ ^ (j + 1)).re) <
        reciprocalSum (n + 2) ‖z‖ := by
      apply Finset.sum_lt_sum (fun j _ => hterm j)
      exact ⟨0, Finset.mem_range.mpr (by omega), by simpa [norm_inv] using hlt⟩
    rw [hre, he, normalized_beta] at hs
    exact lt_irrefl _ hs
  have him : (z⁻¹).im = 0 := by
    have h := Complex.sq_norm_sub_sq_re (z⁻¹)
    rw [hfirst, sub_self, eq_comm, sq_eq_zero_iff] at h
    exact h
  have hinv : z⁻¹ = (((beta n)⁻¹ : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa [norm_inv, he] using hfirst
    · simpa using him
  exact hne (inv_injective (by simpa only [Complex.ofReal_inv] using hinv))

/-- When the cited prefix-ratio limit is supplied, the last step of the
proof of `prop:mbonacci` gives the reciprocal characteristic root. -/
theorem density_of_prefix_ratio (n : Nat) (prefixLength : Nat → Nat)
    (hFischler : Tendsto (fun i => (prefixLength (i + 1) : ℝ) / (prefixLength i : ℝ))
      atTop (𝓝 (beta n))) :
    1 / limsup (fun i => (prefixLength (i + 1) : ℝ) / (prefixLength i : ℝ)) atTop =
      1 / beta n := by
  rw [hFischler.limsup_eq]

end Thesis.MBonacci
