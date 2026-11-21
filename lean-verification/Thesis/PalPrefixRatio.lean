import Thesis.PalindromeDensity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open Filter Topology

namespace Thesis

theorem consecutive_of_enumeration {w : Nat → α} {lengths : Nat → Nat}
    (hmono : StrictMono lengths) (henum : ∀ n, PalPrefix w n ↔ ∃ i, lengths i = n)
    (i : Nat) (hi : 0 < lengths i) :
    ConsecutivePalPrefixes w (lengths i) (lengths (i + 1)) := by
  refine ⟨hi, hmono (Nat.lt_succ_self _), (henum _).2 ⟨i, rfl⟩,
    (henum _).2 ⟨i + 1, rfl⟩, ?_⟩
  intro n hni hin hn
  obtain ⟨j, rfl⟩ := (henum n).1 hn
  have h₁ := hmono.lt_iff_lt.mp hni
  have h₂ := hmono.lt_iff_lt.mp hin
  omega

private theorem consecutive_indices {w : Nat → α} {lengths : Nat → Nat}
    (hmono : StrictMono lengths) (henum : ∀ n, PalPrefix w n ↔ ∃ i, lengths i = n)
    {u v : Nat} (h : ConsecutivePalPrefixes w u v) :
    ∃ i, lengths i = u ∧ lengths (i + 1) = v := by
  obtain ⟨i, rfl⟩ := (henum u).1 h.2.2.1
  obtain ⟨j, rfl⟩ := (henum v).1 h.2.2.2.1
  have hij := hmono.lt_iff_lt.mp h.2.1
  have he : j = i + 1 := by
    by_contra! hne
    have hi := hmono (Nat.lt_succ_self i)
    have hj := hmono (show i + 1 < j by omega)
    exact h.2.2.2.2 _ hi hj ((henum _).2 ⟨i + 1, rfl⟩)
  exact ⟨i, rfl, by rw [he]⟩

private theorem ratio_margin_iff {p q t u v : Nat} (hq : 0 < q) (ht : 0 < t) (hv : 0 < v) :
    (p * t + 1) * v ≤ q * t * u ↔
      (p : ℝ) / q + 1 / ((q : ℝ) * t) ≤ (u : ℝ) / v := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have he : (p : ℝ) / q + 1 / ((q : ℝ) * t) = ((p : ℝ) * t + 1) / ((q : ℝ) * t) := by
    field_simp [hqR.ne', htR.ne']
    ring
  rw [he, div_le_div_iff₀ (mul_pos hqR htR) hvR]
  rw [mul_comm (u : ℝ)]
  exact_mod_cast (Iff.rfl : (p * t + 1) * v ≤ q * t * u ↔ _)

/-- The strict rational lower cut of the liminf of the inverse
ratios of consecutive palindromic prefix lengths. -/
theorem belowPalDensity_iff_of_ratio_liminf {w : Nat → α} {lengths : Nat → Nat}
    (hmono : StrictMono lengths) (henum : ∀ n, PalPrefix w n ↔ ∃ i, lengths i = n)
    {p q : Nat} (hq : 0 < q) :
    BelowPalDensity w p q ↔
      (p : ℝ) / q < liminf (fun i => (lengths i : ℝ) / lengths (i + 1)) atTop := by
  have hpos (i : Nat) : 0 < lengths (i + 1) := by
    exact Nat.zero_lt_of_lt (hmono (show i < i + 1 by omega))
  let ratio : Nat → ℝ := fun i => (lengths i : ℝ) / lengths (i + 1)
  let d := liminf ratio atTop
  change BelowPalDensity w p q ↔ (p : ℝ) / q < d
  have hnonneg (i : Nat) : 0 ≤ ratio i := by dsimp [ratio]; positivity
  have hone (i : Nat) : ratio i ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hpos i)).2
    exact_mod_cast (hmono (show i < i + 1 by omega)).le
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  constructor
  · rintro ⟨_, _, t, ht, K, hK⟩
    have htR : 0 < (t : ℝ) := by exact_mod_cast ht
    have hmargin : ∀ᶠ i in atTop,
        (p : ℝ) / q + 1 / ((q : ℝ) * t) ≤ (lengths i : ℝ) / lengths (i + 1) := by
      filter_upwards [hmono.tendsto_atTop.eventually (eventually_ge_atTop (max 1 K))] with i hi
      have hK' : K ≤ lengths i := (Nat.le_max_right _ _).trans hi
      have hi' : 0 < lengths i := zero_lt_one.trans_le ((Nat.le_max_left _ _).trans hi)
      exact (ratio_margin_iff hq ht (hpos i)).1
        (hK _ _ hK' (consecutive_of_enumeration hmono henum i hi'))
    have he := le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hone) hmargin
    have hposMargin : 0 < 1 / ((q : ℝ) * t) := one_div_pos.mpr (mul_pos hqR htR)
    linarith
  · intro hd
    have hmarginT : Tendsto (fun t : Nat => 1 / ((q : ℝ) * t)) atTop (𝓝 0) := by
      have ht := (tendsto_const_div_atTop_nhds_zero_nat ((q : ℝ)⁻¹))
      simpa only [one_div, mul_inv_rev, div_eq_mul_inv, mul_comm, mul_one] using ht
    have hsmall : ∀ᶠ t : Nat in atTop, 1 / ((q : ℝ) * t) < d - (p : ℝ) / q :=
      hmarginT.eventually (gt_mem_nhds (sub_pos.mpr hd))
    obtain ⟨t, htp, ht⟩ := ((eventually_gt_atTop (0 : Nat)).and hsmall).exists
    have hless : (p : ℝ) / q + 1 / ((q : ℝ) * t) < d := by linarith
    have hlate := eventually_lt_of_lt_liminf hless
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hnonneg))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hlate
    refine ⟨hq, ?_, t, htp, lengths N, ?_⟩
    · intro k
      obtain ⟨i, hi⟩ := (hmono.tendsto_atTop.eventually (eventually_ge_atTop k)).exists
      exact ⟨lengths i, hi, (henum _).2 ⟨i, rfl⟩⟩
    · intro u v hu huv
      obtain ⟨i, rfl, rfl⟩ := consecutive_indices hmono henum huv
      have hi := hmono.le_iff_le.mp hu
      exact (ratio_margin_iff hq htp (hpos i)).2 (hN i hi).le

/-- When the inverse ratios converge, their limit gives the rational cut. -/
theorem belowPalDensity_iff_of_ratio_limit {w : Nat → α} {lengths : Nat → Nat}
    (hmono : StrictMono lengths) (henum : ∀ n, PalPrefix w n ↔ ∃ i, lengths i = n)
    {d : ℝ} (hlim : Tendsto (fun i => (lengths i : ℝ) / lengths (i + 1)) atTop (𝓝 d))
    {p q : Nat} (hq : 0 < q) :
    BelowPalDensity w p q ↔ (p : ℝ) / q < d := by
  rw [belowPalDensity_iff_of_ratio_liminf hmono henum hq, hlim.liminf_eq]

/-- The reciprocal of the limsup of the consecutive-prefix ratios in
Fischler's definition gives the same rational cut. -/
theorem belowPalDensity_iff_of_ratio_limsup {w : Nat → α} {lengths : Nat → Nat}
    (hmono : StrictMono lengths) (henum : ∀ n, PalPrefix w n ↔ ∃ i, lengths i = n)
    (hbound : IsBoundedUnder (· ≤ ·) atTop (fun i => (lengths (i + 1) : ℝ) / lengths i))
    {p q : Nat} (hq : 0 < q) :
    BelowPalDensity w p q ↔
      (p : ℝ) / q < 1 / limsup (fun i => (lengths (i + 1) : ℝ) / lengths i) atTop := by
  let r : Nat → ℝ := fun i => (lengths (i + 1) : ℝ) / lengths i
  let f : ℝ → ℝ := fun x => 1 / max 1 x
  have hmax (x : ℝ) : 0 < max 1 x := zero_lt_one.trans_le (le_max_left _ _)
  have hcont : Continuous f := continuous_const.div (continuous_const.max continuous_id)
    (fun x => (hmax x).ne')
  have hanti : Antitone f := fun x y hxy =>
    one_div_le_one_div_of_le (hmax x) (max_le_max le_rfl hxy)
  have hpos : ∀ᶠ i in atTop, 0 < (lengths i : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : Nat)] with i hi
    exact_mod_cast Nat.zero_lt_of_lt (hmono hi)
  have hge : ∀ᶠ i in atTop, 1 ≤ r i := by
    filter_upwards [hpos] with i hi
    exact (le_div_iff₀ hi).2 (by
      rw [one_mul]
      exact_mod_cast (hmono (show i < i + 1 by omega)).le)
  have hlimsup : 1 ≤ limsup r atTop :=
    le_limsup_of_frequently_le hge.frequently hbound
  have hmap := hanti.map_limsup_of_continuousAt r hcont.continuousAt hbound
    (isCoboundedUnder_le_of_eventually_le atTop hge)
  have he : liminf (f ∘ r) atTop = liminf (fun i => (lengths i : ℝ) / lengths (i + 1)) atTop := by
    apply liminf_congr
    filter_upwards [hge] with i hi
    simp only [Function.comp_apply, f, max_eq_right hi, one_div, r, inv_div]
  rw [belowPalDensity_iff_of_ratio_liminf hmono henum hq, ← he, ← hmap]
  dsimp only [f]
  rw [max_eq_right hlimsup]

end Thesis
