import Thesis.SturmianConstantTail
import Thesis.PalPrefixRatio
import Thesis.SturmianDiophantine

open Filter Topology

namespace Thesis.SturmianDensity

/-- The upper bound in `cor:palSturm` (1), using the cited lower bound
on Fischler's consecutive-prefix ratio. -/
theorem density_le_golden_reciprocal (s : ReversedFractions)
    (hFischler : goldenRatio ≤ limsup s.peak atTop) :
    s.fischlerDensity ≤ 1 / goldenRatio := by
  have hφ : 0 < goldenRatio := by unfold goldenRatio; positivity
  exact one_div_le_one_div_of_le hφ hFischler

private theorem reciprocal_second_peak :
    1 / (1 + Real.sqrt 2 / 2) = 2 - Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : 0 < 1 + Real.sqrt 2 / 2 := by positivity
  apply (div_eq_iff hp.ne').2
  nlinarith only [hs]

private theorem second_density_lt_golden :
    2 - Real.sqrt 2 < 1 / goldenRatio := by
  have hs₂ : (7 : ℝ) / 5 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs₅ : Real.sqrt 5 < (7 : ℝ) / 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hφ : 0 < goldenRatio := by unfold goldenRatio; positivity
  have hφ' : goldenRatio < (5 : ℝ) / 3 := by unfold goldenRatio; linarith
  have h := one_div_lt_one_div_of_lt hφ hφ'
  have ha : 2 - Real.sqrt 2 < (3 : ℝ) / 5 := by linarith
  have he : 1 / ((5 : ℝ) / 3) = 3 / 5 := by norm_num
  exact ha.trans (he ▸ h)

/-- The gap in `cor:palSturm` (4), under the quoted
Fischler–Cassaigne spectral bound for a tail which is not eventually one. -/
theorem density_le_second_value_of_spectral_gap (s : ReversedFractions)
    (hgap : 1 + Real.sqrt 2 / 2 ≤ limsup s.peak atTop) :
    s.fischlerDensity ≤ 2 - Real.sqrt 2 := by
  rw [← reciprocal_second_peak]
  exact one_div_le_one_div_of_le (by positivity) hgap

private theorem second_peak_of_small_tail (s : ReversedFractions) {k : Nat}
    (ht : s.t (k + 1) ≤ 2 / 5) : 1 + Real.sqrt 2 / 2 ≤ s.peak k := by
  have hs : Real.sqrt 2 < (10 : ℝ) / 7 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hp : 0 < (1 : ℝ) + s.t (k + 1) := by linarith [(s.t_bounds (k + 1)).1]
  have h := one_div_le_one_div_of_le hp
    (show (1 : ℝ) + s.t (k + 1) ≤ 1 + 2 / 5 by linarith)
  norm_num at h
  unfold ReversedFractions.peak
  rw [one_div]
  linarith

private theorem second_peak_of_large_digit (s : ReversedFractions) (k : Nat) (h : 3 ≤ s.a k) :
    1 + Real.sqrt 2 / 2 ≤ s.peak k := by
  apply second_peak_of_small_tail s
  have ha : (3 : ℝ) ≤ s.a k := by exact_mod_cast h
  rw [s.step]
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
    (by linarith [(s.t_bounds k).1])).trans (by norm_num)

private theorem second_peak_of_one_two (s : ReversedFractions) (i : Nat)
    (h₁ : s.a i = 1) (h₂ : s.a (i + 1) = 2) : 1 + Real.sqrt 2 / 2 ≤ s.peak (i + 1) := by
  apply second_peak_of_small_tail s
  have ht : (1 : ℝ) / 2 ≤ s.t (i + 1) := by
    rw [s.step, h₁, Nat.cast_one]
    exact one_div_le_one_div_of_le (by linarith [(s.t_bounds i).1])
      (by linarith [(s.t_bounds i).2])
  rw [s.step, h₂]
  norm_num only [Nat.cast_ofNat]
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 2 + s.t (i + 1))).2
  linarith

private theorem second_peak_limsup_of_frequent (s : ReversedFractions)
    (h : ∀ N : Nat, ∃ k ≥ N, 1 + Real.sqrt 2 / 2 ≤ s.peak k) :
    1 + Real.sqrt 2 / 2 ≤ limsup s.peak atTop := by
  refine le_limsup_of_frequently_le (frequently_atTop.2 h) ?_
  apply isBoundedUnder_of_eventually_le (a := (2 : ℝ))
  apply Eventually.of_forall
  intro k
  have ht := (s.t_bounds (k + 1)).1
  have he : 1 / (1 + s.t (k + 1)) ≤ 1 :=
    div_le_one_of_le₀ (by linarith) (by linarith)
  unfold ReversedFractions.peak
  linarith

/-- The Fischler–Cassaigne gap used in the source, restricted to the
peak sequence of a characteristic Sturmian slope. For nonconstant
tails using only 1 and 2, the transitions from 1 to 2 supply the peaks. -/
theorem peak_gap_of_not_eventually_one (s : ReversedFractions)
    (h : ¬ ∃ N, ∀ k ≥ N, s.a k = 1) :
    1 + Real.sqrt 2 / 2 ≤ limsup s.peak atTop := by
  classical
  by_cases hb : ∃ N, ∀ k ≥ N, s.a k ≤ 2
  · obtain ⟨B, hB⟩ := hb
    by_cases hn : ∃ N, ∀ k ≥ N, s.a k ≠ 1
    · obtain ⟨C, hC⟩ := hn
      have ht : ∀ k ≥ max B C, s.a k = 2 := by
        intro k hk
        have h₁ := hB k ((Nat.le_max_left _ _).trans hk)
        have h₂ := hC k ((Nat.le_max_right _ _).trans hk)
        have h₃ := s.a_pos k
        omega
      have he := density_twos_tail s (max B C) ht
      rw [ReversedFractions.fischlerDensity, ← reciprocal_second_peak] at he
      exact (inv_injective (by simpa only [one_div] using he)).symm.le
    · apply second_peak_limsup_of_frequent s
      intro N
      have hone : ∃ i ≥ max N B, s.a i = 1 := by
        by_contra! hno
        exact hn ⟨max N B, hno⟩
      obtain ⟨i, hi, hi₁⟩ := hone
      have hnon : ∃ j, s.a (i + j + 1) ≠ 1 := by
        by_contra! hno
        apply h
        refine ⟨i + 1, fun k hk => ?_⟩
        have he := hno (k - (i + 1))
        have hind : i + (k - (i + 1)) + 1 = k := by omega
        simpa only [hind] using he
      let j := Nat.find hnon
      have hj := Nat.find_spec hnon
      have hprev : s.a (i + j) = 1 := by
        rcases Nat.eq_zero_or_pos j with hz | hp
        · simpa [hz] using hi₁
        · by_contra hneq
          have he : i + (j - 1) + 1 = i + j := by omega
          have hbefore : s.a (i + (j - 1) + 1) ≠ 1 := he.symm ▸ hneq
          exact (not_le_of_gt (show j - 1 < j by omega)) (Nat.find_min' hnon hbefore)
      have htwo : s.a (i + j + 1) = 2 := by
        have hb' := hB (i + j + 1) ((Nat.le_max_right _ _).trans (hi.trans (by omega)))
        have hp := s.a_pos (i + j + 1)
        change s.a (i + j + 1) ≠ 1 at hj
        omega
      exact ⟨i + j + 1, (Nat.le_max_left _ _).trans (hi.trans (by omega)),
        second_peak_of_one_two s (i + j) hprev htwo⟩
  · apply second_peak_limsup_of_frequent s
    intro N
    have hlarge : ∃ k ≥ N, 3 ≤ s.a k := by
      by_contra! hno
      exact hb ⟨N, fun k hk => by have he := hno k hk; omega⟩
    obtain ⟨k, hk, h₃⟩ := hlarge
    exact ⟨k, hk, second_peak_of_large_digit s k h₃⟩

/-- The top value is attained exactly for eventually all-one partial
quotients, using the spectral gap cited in `cor:palSturm` (4). -/
theorem density_eq_golden_reciprocal_iff (s : ReversedFractions) :
    s.fischlerDensity = 1 / goldenRatio ↔ ∃ N, ∀ k ≥ N, s.a k = 1 := by
  classical
  constructor
  · intro he
    by_contra hn
    have hgap := density_le_second_value_of_spectral_gap s (peak_gap_of_not_eventually_one s hn)
    rw [he] at hgap
    exact (not_le_of_gt second_density_lt_golden) hgap
  · rintro ⟨N, h⟩
    exact density_ones_tail s N h

/-- The global bound in this Sturmian class, including the equality
case supplied by the one-tail computation. -/
theorem density_bounds (s : ReversedFractions) :
    1 / 2 ≤ s.fischlerDensity ∧ s.fischlerDensity ≤ 1 / goldenRatio := by
  classical
  refine ⟨half_le_density s, ?_⟩
  by_cases h : ∃ N, ∀ k ≥ N, s.a k = 1
  · exact ((density_eq_golden_reciprocal_iff s).2 h).le
  · exact (density_le_second_value_of_spectral_gap s
      (peak_gap_of_not_eventually_one s h)).trans second_density_lt_golden.le

/-- Connecting the cited Fischler formula to the rational-cut
definition for a word, given the enumeration of its palindromic prefixes. -/
theorem below_density_iff_of_fischler_formula (s : ReversedFractions)
    (w : Nat → α) (lengths : Nat → Nat) (hmono : StrictMono lengths)
    (henum : ∀ k, PalPrefix w k ↔ ∃ i, lengths i = k)
    (hFischler : limsup (fun i => (lengths (i + 1) : ℝ) / lengths i) atTop =
      limsup s.peak atTop) {p q : Nat} (hq : 0 < q) :
    BelowPalDensity w p q ↔ (p : ℝ) / q < s.fischlerDensity := by
  classical
  let ratio : Nat → ℝ := fun i => (lengths (i + 1) : ℝ) / lengths i
  have hpos : 0 < limsup ratio atTop := by
    change 0 < limsup (fun i => (lengths (i + 1) : ℝ) / lengths i) atTop
    rw [hFischler]
    exact one_div_pos.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (half_le_density s))
  have hb : IsBoundedUnder (· ≤ ·) atTop ratio := by
    by_contra hn
    have he : {b : ℝ | ∀ᶠ i in atTop, ratio i ≤ b} = ∅ := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hn (isBoundedUnder_of_eventually_le h)
    rw [limsup_eq, he, Real.sInf_empty] at hpos
    exact (lt_irrefl _ hpos)
  rw [belowPalDensity_iff_of_ratio_limsup hmono henum hb hq, hFischler]
  rfl

/-- The diophantine conclusion of `prop:dichotomy` in the word-level
density representation, with Fischler's formula as the cited input. -/
theorem word_density_gt_half_iff_badlyApproximable {a : ℝ} (ha : Irrational a)
    (w : Nat → α) (lengths : Nat → Nat) (hmono : StrictMono lengths)
    (henum : ∀ k, PalPrefix w k ↔ ∃ i, lengths i = k)
    (hFischler : limsup (fun i => (lengths (i + 1) : ℝ) / lengths i) atTop =
      limsup (slopeFractions a ha).peak atTop) :
    BelowPalDensity w 1 2 ↔ BadlyApproximable a := by
  rw [below_density_iff_of_fischler_formula (slopeFractions a ha) w lengths hmono henum
    hFischler (by omega)]
  simpa only [Nat.cast_one, Nat.cast_ofNat] using slope_density_gt_half_iff ha

/-- Separator insertion gives the same rational cut of the Sturmian
density, as in `cor:palSturm` (6). -/
theorem below_inserted_density_iff_of_fischler_formula (s : ReversedFractions)
    (w : Nat → α) (lengths : Nat → Nat) (hmono : StrictMono lengths)
    (henum : ∀ k, PalPrefix w k ↔ ∃ i, lengths i = k)
    (hFischler : limsup (fun i => (lengths (i + 1) : ℝ) / lengths i) atTop =
      limsup s.peak atTop) {p q : Nat} (hq : 0 < q) :
    BelowPalDensity (insertSeparator w) p q ↔ (p : ℝ) / q < s.fischlerDensity :=
  (palDensity_insert w p q).trans
    (below_density_iff_of_fischler_formula s w lengths hmono henum hFischler hq)

end Thesis.SturmianDensity
