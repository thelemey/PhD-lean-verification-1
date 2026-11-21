import Thesis.PalPrefixRatio
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Set Filter Topology
open scoped ENNReal

namespace Thesis

/-- The density from the thesis, using the increasing enumeration of
palindromic prefix lengths. An infinite limsup of length ratios has
reciprocal zero. -/
noncomputable def palindromicDensity (w : Nat → α) : ℝ := by
  classical
  exact if {n | PalPrefix w n}.Infinite then
    let L := Nat.nth (PalPrefix w)
    ((limsup (fun i => (L (i + 1) : ℝ≥0∞) / L i) atTop)⁻¹).toReal
  else 0

theorem palindromicDensity_of_finite {w : Nat → α}
    (h : {n | PalPrefix w n}.Finite) : palindromicDensity w = 0 := by
  simp only [palindromicDensity, if_neg (not_infinite.2 h)]

private theorem inverseRatios_bounds {L : Nat → Nat} (hL : StrictMono L) :
    ∀ i, 0 ≤ (L i : ℝ) / L (i + 1) ∧ (L i : ℝ) / L (i + 1) ≤ 1 := by
  intro i
  have hi := hL (Nat.lt_succ_self i)
  refine ⟨by positivity, (div_le_one (by exact_mod_cast (Nat.zero_lt_of_lt hi))).2 ?_⟩
  exact_mod_cast hi.le

private theorem liminf_inverseRatios_nonneg {L : Nat → Nat} (hL : StrictMono L) :
    0 ≤ liminf (fun i => (L i : ℝ) / L (i + 1)) atTop :=
  le_liminf_of_le (isCoboundedUnder_ge_of_le atTop fun i => (inverseRatios_bounds hL i).2)
    (Eventually.of_forall fun i => (inverseRatios_bounds hL i).1)

/-- On an infinite set of prefix lengths, the reciprocal limsup in the
definition agrees with the liminf of inverse ratios. -/
private theorem reciprocal_limsup_eq_liminf {L : Nat → Nat} (hL : StrictMono L) :
    ((limsup (fun i => (L (i + 1) : ℝ≥0∞) / L i) atTop)⁻¹).toReal =
      liminf (fun i => (L i : ℝ) / L (i + 1)) atTop := by
  let r := fun i => (L i : ℝ) / L (i + 1)
  have hlo : atTop.IsBoundedUnder (· ≥ ·) r :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun i => (inverseRatios_bounds hL i).1)
  have hhi : atTop.IsCoboundedUnder (· ≥ ·) r :=
    isCoboundedUnder_ge_of_le atTop fun i => (inverseRatios_bounds hL i).2
  have hmono : Monotone ENNReal.ofReal := fun _ _ => ENNReal.ofReal_le_ofReal
  have hmap := hmono.map_liminf_of_continuousAt r
    ENNReal.continuous_ofReal.continuousAt hhi hlo
  rw [ENNReal.inv_limsup]
  have he : liminf (fun i => ((L (i + 1) : ℝ≥0∞) / L i)⁻¹) atTop =
      liminf (ENNReal.ofReal ∘ r) atTop := by
    apply liminf_congr
    filter_upwards [] with i
    have hp : 0 < L (i + 1) := Nat.zero_lt_of_lt (hL (Nat.lt_succ_self i))
    simp only [Function.comp_apply, r, ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 hp),
      ENNReal.ofReal_natCast]
    exact ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top (L i))) (Or.inr (Nat.cast_ne_zero.2 hp.ne'))
  rw [he, ← hmap, ENNReal.toReal_ofReal (liminf_inverseRatios_nonneg hL)]

/-- The exact real density has the rational cut used by the word-level proofs. -/
theorem belowPalDensity_iff_lt_palindromicDensity (w : Nat → α) {p q : Nat} (hq : 0 < q) :
    BelowPalDensity w p q ↔ (p : ℝ) / q < palindromicDensity w := by
  classical
  by_cases h : {n | PalPrefix w n}.Infinite
  · have henum (n : Nat) : PalPrefix w n ↔ ∃ i, Nat.nth (PalPrefix w) i = n := by
      change n ∈ {n | PalPrefix w n} ↔ _
      rw [← Nat.range_nth_of_infinite h]
      rfl
    have hL := Nat.nth_strictMono h
    rw [belowPalDensity_iff_of_ratio_liminf hL henum hq]
    simp only [palindromicDensity, if_pos h, reciprocal_limsup_eq_liminf hL]
  · rw [palindromicDensity_of_finite (not_infinite.1 h)]
    refine ⟨fun hb => ?_, fun hr => False.elim ((not_lt_of_ge (by positivity)) hr)⟩
    obtain ⟨N, hN⟩ := (not_infinite.1 h).bddAbove
    obtain ⟨n, hn, hp⟩ := hb.2.1 (N + 1)
    exact False.elim (by have := hN hp; omega)

theorem palindromicDensity_nonneg (w : Nat → α) : 0 ≤ palindromicDensity w := by
  classical
  unfold palindromicDensity
  split
  · exact ENNReal.toReal_nonneg
  · rfl

theorem palindromicDensity_le_one (w : Nat → α) : palindromicDensity w ≤ 1 := by
  classical
  by_cases h : {n | PalPrefix w n}.Infinite
  · have hL := Nat.nth_strictMono h
    simp only [palindromicDensity, if_pos h, reciprocal_limsup_eq_liminf hL]
    exact liminf_le_of_frequently_le
      (Eventually.of_forall fun i => (inverseRatios_bounds hL i).2).frequently
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun i => (inverseRatios_bounds hL i).1))
  · rw [palindromicDensity_of_finite (not_infinite.1 h)]
    exact zero_le_one

private theorem exists_nat_ratio_between {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    ∃ p q : Nat, 0 < q ∧ x < (p : ℝ) / q ∧ (p : ℝ) / q < y := by
  obtain ⟨s, hxs, hsy⟩ := exists_rat_btwn hxy
  have hs : 0 ≤ s := by exact_mod_cast hx.trans hxs.le
  have hn := Int.toNat_of_nonneg (Rat.num_nonneg.2 hs)
  have hnR : (s.num.toNat : ℝ) = (s.num : ℝ) := by exact_mod_cast hn
  have he : (s : ℝ) = (s.num.toNat : ℝ) / s.den := by
    rw [Rat.cast_def, hnR]
  rw [he] at hxs hsy
  exact ⟨s.num.toNat, s.den, s.pos, hxs, hsy⟩

/-- The rational cut determines the exact value of the density. -/
theorem palindromicDensity_eq_of_cut {w : Nat → α} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ p q : Nat, 0 < q → (BelowPalDensity w p q ↔ (p : ℝ) / q < d)) :
    palindromicDensity w = d := by
  apply le_antisymm
  · by_contra! hlt
    obtain ⟨p, q, hq, hlo, hhi⟩ := exists_nat_ratio_between hd hlt
    exact (not_lt_of_ge hlo.le) ((h p q hq).1 ((belowPalDensity_iff_lt_palindromicDensity w hq).2 hhi))
  · by_contra! hlt
    obtain ⟨p, q, hq, hlo, hhi⟩ := exists_nat_ratio_between (palindromicDensity_nonneg w) hlt
    exact (not_lt_of_ge hlo.le) ((belowPalDensity_iff_lt_palindromicDensity w hq).1 ((h p q hq).2 hhi))

/-- Any increasing enumeration of the palindromic prefix lengths can
be used to evaluate the density defined by the canonical enumeration. -/
theorem palindromicDensity_eq_reciprocal_limsup {w : Nat → α} {L : Nat → Nat}
    (hL : StrictMono L) (henum : ∀ k, PalPrefix w k ↔ ∃ i, L i = k) :
    palindromicDensity w =
      ((limsup (fun i => (L (i + 1) : ℝ≥0∞) / L i) atTop)⁻¹).toReal := by
  rw [reciprocal_limsup_eq_liminf hL]
  exact palindromicDensity_eq_of_cut (liminf_inverseRatios_nonneg hL)
    fun _ _ hq => belowPalDensity_iff_of_ratio_liminf hL henum hq

/-- Insertion preserves the real-valued density, including the finite case. -/
theorem palindromicDensity_insert (w : Nat → α) :
    palindromicDensity (insertSeparator w) = palindromicDensity w :=
  palindromicDensity_eq_of_cut (palindromicDensity_nonneg w) fun p q hq =>
    (palDensity_insert w p q).trans (belowPalDensity_iff_lt_palindromicDensity w hq)

end Thesis
