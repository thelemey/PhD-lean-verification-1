import Thesis.PalindromePrefixBlocks
import Thesis.SturmianDensitySpectrum
import Thesis.SturmianMechanical
import Mathlib.Data.Nat.Nth

open Filter Topology Set

namespace Thesis.SturmianDensity

/-- Natural continuant denominators, starting with the customary pair
(0,1). The zero-based quotient sequence begins at a₁. -/
def continuedDenominator (s : ReversedFractions) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | k + 2 => s.a k * continuedDenominator s (k + 1) + continuedDenominator s k

theorem continuedDenominator_pos (s : ReversedFractions) (k : Nat) :
    0 < continuedDenominator s (k + 1) := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    change 0 < s.a k * continuedDenominator s (k + 1) + continuedDenominator s k
    exact Nat.add_pos_left (Nat.mul_pos (s.a_pos k) ih) _

private theorem continuedDenominator_step_gt (s : ReversedFractions) (k : Nat) :
    continuedDenominator s (k + 2) < continuedDenominator s (k + 3) := by
  change continuedDenominator s (k + 2) <
    s.a (k + 1) * continuedDenominator s (k + 2) + continuedDenominator s (k + 1)
  have h := Nat.mul_le_mul_right (continuedDenominator s (k + 2)) (s.a_pos (k + 1))
  simp only [one_mul] at h
  have := continuedDenominator_pos s k
  omega

theorem reversed_t_eq_continuedDenominator (s : ReversedFractions) (hzero : s.t 0 = 0)
    (k : Nat) : s.t k = (continuedDenominator s k : ℝ) / continuedDenominator s (k + 1) := by
  induction k with
  | zero => simp [continuedDenominator, hzero]
  | succ k ih =>
    have hpos : 0 < (continuedDenominator s (k + 1) : ℝ) := by
      exact_mod_cast continuedDenominator_pos s k
    have hnext : 0 < (continuedDenominator s (k + 2) : ℝ) := by
      exact_mod_cast continuedDenominator_pos s (k + 1)
    have hsum : 0 < (s.a k : ℝ) +
        (continuedDenominator s k : ℝ) / continuedDenominator s (k + 1) :=
      add_pos_of_pos_of_nonneg (by exact_mod_cast s.a_pos k) (by positivity)
    rw [s.step, ih]
    apply (div_eq_div_iff hsum.ne' hnext.ne').2
    change 1 * (continuedDenominator s (k + 2) : ℝ) =
      (continuedDenominator s (k + 1) : ℝ) *
        ((s.a k : ℝ) + (continuedDenominator s k : ℝ) / continuedDenominator s (k + 1))
    have he : continuedDenominator s (k + 2) =
        s.a k * continuedDenominator s (k + 1) + continuedDenominator s k := rfl
    rw [he, Nat.cast_add, Nat.cast_mul, one_mul, mul_add, mul_div_cancel₀ _ hpos.ne', mul_comm]

/-- The natural denominators used in the length blocks are exactly
the denominators of the continued-fraction approximants in mathlib. -/
theorem continuedDenominator_eq_contsAux {a : ℝ} (ha : Irrational a) (n : Nat) :
    (continuedDenominator (slopeFractions a ha) n : ℝ) =
      ((GenContFract.of a).contsAux n).b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [continuedDenominator, GenContFract.contsAux]
    · simp [continuedDenominator, GenContFract.contsAux]
    · have he : continuedDenominator (slopeFractions a ha) (n + 2) =
          partialQuotient a n * continuedDenominator (slopeFractions a ha) (n + 1) +
            continuedDenominator (slopeFractions a ha) n := rfl
      rw [he, Nat.cast_add, Nat.cast_mul, ih (n + 1) (by omega), ih n (by omega)]
      exact (slope_contsAux_den_step ha n).symm

/-- Ignore the first two blocks, so all the remaining palindrome
lengths are positive and the denominators increase strictly. -/
def ReversedFractions.prefixBlocks (s : ReversedFractions) : PalindromePrefixBlocks where
  Q k := continuedDenominator s (k + 2)
  d k := s.a (k + 2)
  positive k := continuedDenominator_pos s (k + 1)
  increasing := strictMono_nat_of_lt_succ (continuedDenominator_step_gt s)
  step _ := rfl
  digit_pos k := s.a_pos (k + 2)

private theorem denominator_peak_eq (s : ReversedFractions) (hzero : s.t 0 = 0) (k : Nat) :
    s.peak (k + 1) =
      1 + ((s.prefixBlocks.Q (k + 1) : ℝ) / (s.prefixBlocks.Q k + s.prefixBlocks.Q (k + 1))) := by
  have hpos : 0 < (s.prefixBlocks.Q (k + 1) : ℝ) := by
    exact_mod_cast s.prefixBlocks.positive (k + 1)
  have hsum : 0 < (s.prefixBlocks.Q k + s.prefixBlocks.Q (k + 1) : ℝ) := by positivity
  have hratio : s.t (k + 1 + 1) =
      (s.prefixBlocks.Q k : ℝ) / s.prefixBlocks.Q (k + 1) :=
    reversed_t_eq_continuedDenominator s hzero (k + 2)
  rw [ReversedFractions.peak, hratio]
  congr 1
  apply (div_eq_div_iff (by positivity) hsum.ne').2
  rw [one_mul, mul_add, mul_one, mul_div_cancel₀ _ hpos.ne']
  ring

private theorem rawPeak_diff_bounds (s : ReversedFractions) (hzero : s.t 0 = 0) (k : Nat) :
    0 ≤ s.prefixBlocks.rawPeak k - s.peak (k + 1) ∧
      s.prefixBlocks.rawPeak k - s.peak (k + 1) ≤ 2 / (s.prefixBlocks.first k : ℝ) := by
  let x : ℝ := s.prefixBlocks.Q (k + 1)
  let y : ℝ := s.prefixBlocks.Q k
  let z : ℝ := s.prefixBlocks.first k
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hy : 0 ≤ y := Nat.cast_nonneg _
  have hz : 0 < z := by
    change (0 : ℝ) < (s.prefixBlocks.first k : ℝ)
    exact_mod_cast s.prefixBlocks.first_pos k
  have hsum : 0 < y + x := by
    have h : 0 < x := by
      change (0 : ℝ) < (s.prefixBlocks.Q (k + 1) : ℝ)
      exact_mod_cast s.prefixBlocks.positive (k + 1)
    exact add_pos_of_nonneg_of_pos hy h
  have hz' : z = y + x - 2 := by
    have h : 2 ≤ s.prefixBlocks.Q (k + 1) + s.prefixBlocks.Q k := by
      have := s.prefixBlocks.Q_next_ge_two k
      omega
    dsimp only [z, PalindromePrefixBlocks.first, PalindromePrefixBlocks.len]
    rw [one_mul, Nat.cast_sub h, Nat.cast_add, Nat.cast_ofNat]
    change x + y - 2 = y + x - 2
    ring
  rw [denominator_peak_eq s hzero, PalindromePrefixBlocks.rawPeak]
  change 0 ≤ (1 + x / z) - (1 + x / (y + x)) ∧ _ ≤ 2 / z
  have he : (1 + x / z) - (1 + x / (y + x)) = (x / (y + x)) * (2 / z) := by
    calc
      _ = x * (y + x - z) / (z * (y + x)) := by field_simp [hz.ne', hsum.ne']; ring
      _ = _ := by
        rw [show y + x - z = 2 by linarith]
        rw [div_mul_div_comm, mul_comm z (y + x)]
  rw [he]
  exact ⟨mul_nonneg (div_nonneg hx hsum.le) (by positivity),
    mul_le_of_le_one_left (by positivity) ((div_le_one hsum).2 (by linarith))⟩

/-- The subtraction of two in the palindrome lengths has vanishing
effect on the ratio at the first length of a block. -/
theorem limsup_rawPeak_eq_peak (s : ReversedFractions) (hzero : s.t 0 = 0) :
    limsup s.prefixBlocks.rawPeak atTop = limsup s.peak atTop := by
  let f := s.prefixBlocks.rawPeak
  let g : Nat → ℝ := fun k => s.peak (k + 1)
  have hgb (k : Nat) : 1 ≤ g k ∧ g k ≤ 2 := by
    have ht := (s.t_bounds (k + 1 + 1)).1
    have hpos : 0 < 1 + s.t (k + 1 + 1) := by linarith
    have h := (div_le_one hpos).2 (by linarith : (1 : ℝ) ≤ 1 + s.t (k + 1 + 1))
    have hn := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hpos.le
    change 1 ≤ 1 + 1 / (1 + s.t (k + 1 + 1)) ∧ 1 + 1 / (1 + s.t (k + 1 + 1)) ≤ 2
    exact ⟨by linarith, by linarith⟩
  have hfb (k : Nat) : 1 ≤ f k ∧ f k ≤ 4 := by
    obtain ⟨h₁, h₂⟩ := rawPeak_diff_bounds s hzero k
    have hfirst : 1 ≤ (s.prefixBlocks.first k : ℝ) := by exact_mod_cast s.prefixBlocks.first_pos k
    have hfrac : (2 : ℝ) / s.prefixBlocks.first k ≤ 2 := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < s.prefixBlocks.first k)).2
      linarith
    change 0 ≤ f k - g k at h₁
    change f k - g k ≤ _ at h₂
    exact ⟨by linarith [(hgb k).1], by linarith [(hgb k).2]⟩
  have hCof := isCoboundedUnder_le_of_le atTop (fun k => (hfb k).1)
  have hCog := isCoboundedUnder_le_of_le atTop (fun k => (hgb k).1)
  have hBf : IsBoundedUnder (· ≤ ·) atTop f :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun k => (hfb k).2)
  have hBg : IsBoundedUnder (· ≤ ·) atTop g :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun k => (hgb k).2)
  have hzero' : Tendsto (fun k => 2 / (s.prefixBlocks.first k : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 2).comp s.prefixBlocks.first_strictMono.tendsto_atTop
  have he : limsup f atTop = limsup g atTop := by
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hlim := eventually_lt_of_limsup_lt (show limsup g atTop < limsup g atTop + ε / 2 by linarith) hBg
      have hsmall := hzero'.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
      apply limsup_le_of_le hCof
      filter_upwards [hlim, hsmall] with k hk hq
      have h := (rawPeak_diff_bounds s hzero k).2
      change f k - g k ≤ _ at h
      linarith
    · apply limsup_le_limsup _ hCog hBf
      exact Eventually.of_forall fun k => sub_nonneg.1 (rawPeak_diff_bounds s hzero k).1
  exact he.trans (limsup_nat_add s.peak 1)

/-- Fischler's ratio formula follows from the large-length part of the
palindrome-prefix enumeration. The finite initial lengths can vary. -/
theorem below_density_iff_of_palindrome_blocks (s : ReversedFractions) (hzero : s.t 0 = 0)
    (w : Nat → α) {K : Nat}
    (hBlocks : ∀ L ≥ K, PalPrefix w L ↔ ∃ k m,
      1 ≤ m ∧ m ≤ s.prefixBlocks.d k ∧ s.prefixBlocks.len k m = L)
    {p q : Nat} (hq : 0 < q) :
    BelowPalDensity w p q ↔ (p : ℝ) / q < s.fischlerDensity := by
  classical
  obtain ⟨k₀, hk₀⟩ := (s.prefixBlocks.first_strictMono.tendsto_atTop.eventually
    (eventually_ge_atTop K)).exists
  have hinf : {k : Nat | PalPrefix w k}.Infinite := by
    apply (Set.infinite_range_of_injective (f := fun k => s.prefixBlocks.first (k + k₀))
      (fun _ _ he => Nat.add_right_cancel (s.prefixBlocks.first_strictMono.injective he))).mono
    rintro L ⟨k, rfl⟩
    have hh : K ≤ s.prefixBlocks.first (k + k₀) :=
      hk₀.trans (s.prefixBlocks.first_strictMono.monotone (by omega))
    exact (hBlocks _ hh).2 ⟨k + k₀, 1, le_rfl, s.prefixBlocks.digit_pos _, rfl⟩
  let P := Nat.nth (PalPrefix w)
  have hen (L : Nat) : PalPrefix w L ↔ ∃ i, P i = L := by
    change L ∈ {k : Nat | PalPrefix w k} ↔ L ∈ Set.range P
    rw [Nat.range_nth_of_infinite hinf]
  apply below_density_iff_of_fischler_formula s w P (Nat.nth_strictMono hinf) hen _ hq
  rw [s.prefixBlocks.limsup_ratios_eq_rawPeak (Nat.nth_strictMono hinf)
    (fun L hL => (hen L).symm.trans (hBlocks L hL)), limsup_rawPeak_eq_peak s hzero]

/-- The slope criterion for the actual mechanical word, conditional on
the cited enumeration of its sufficiently long palindromic prefixes. -/
theorem characteristic_density_gt_half_of_palindrome_blocks {a : ℝ} (ha : Irrational a) {K : Nat}
    (hBlocks : ∀ L ≥ K, PalPrefix (FactorTree.characteristicWord a) L ↔
      ∃ k m, 1 ≤ m ∧ m ≤ (slopeFractions a ha).prefixBlocks.d k ∧
        (slopeFractions a ha).prefixBlocks.len k m = L) :
    BelowPalDensity (FactorTree.characteristicWord a) 1 2 ↔ BadlyApproximable a := by
  rw [below_density_iff_of_palindrome_blocks (slopeFractions a ha) rfl _ hBlocks (by omega)]
  simpa only [Nat.cast_one, Nat.cast_ofNat] using slope_density_gt_half_iff ha

end Thesis.SturmianDensity
