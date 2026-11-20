import Thesis.FactorialLeadingDigits
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace Thesis.FactorialWord

private theorem factorial_ge (n : Nat) : n ≤ factorial n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [factorial]
    simpa using Nat.mul_le_mul_left (n + 1) (factorial_pos n)

private theorem digits_length_positive {b n : Nat} (hb : 1 < b) (hn : 0 < n) :
    0 < (digits b n).length := by rw [digits_step hb hn]; simp

/-- A positive number with (m) canonical base-(b) digits lies
between (b^{m-1}) and (b^m). -/
theorem digits_power_bounds {b : Nat} (hb : 1 < b) (n : Nat) (hn : 0 < n) :
    b ^ ((digits b n).length - 1) ≤ n ∧ n < b ^ (digits b n).length := by
  let q := n / b
  have hi := Nat.mod_add_div n b
  have hr := Nat.mod_lt n (show 0 < b by omega)
  change n % b + b * q = n at hi
  rw [digits_step hb hn, List.length_cons, Nat.add_sub_cancel]
  by_cases hq : q = 0
  · change n / b = 0 at hq
    rw [hq, digits_zero]
    simp only [List.length_nil, pow_zero, zero_add, pow_one]
    rw [show q = 0 from hq, Nat.mul_zero] at hi
    omega
  · have hq0 : 0 < q := Nat.pos_of_ne_zero hq
    have ⟨hlo, hhi⟩ := digits_power_bounds hb q hq0
    have hlen : 0 < (digits b q).length := digits_length_positive hb hq0
    change b ^ (digits b q).length ≤ n ∧ n < b ^ ((digits b q).length + 1)
    constructor
    · have hp := Nat.mul_le_mul_left b hlo
      rw [← Nat.pow_succ', show ((digits b q).length - 1).succ = (digits b q).length by omega] at hp
      omega
    · have hp := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hhi)
      rw [Nat.mul_succ, ← Nat.pow_succ', Nat.succ_eq_add_one] at hp
      omega
termination_by n
decreasing_by exact Nat.div_lt_self hn hb

open Real

private theorem logb_nat_power {b : Nat} (hb : 1 < b) (k : Nat) :
    logb (b : ℝ) ((b ^ k : Nat) : ℝ) = (k : ℝ) := by
  rw [Nat.cast_pow, logb_pow, logb_self_eq_one (by exact_mod_cast hb), mul_one]

private theorem logb_scaled_nat {b u : Nat} (hb : 1 < b) (hu : 0 < u) (p : Nat) :
    logb (b : ℝ) ((u * b ^ p : Nat) : ℝ) = logb (b : ℝ) (u : ℝ) + p := by
  rw [Nat.cast_mul, logb_mul (by exact_mod_cast hu.ne')
    (by exact_mod_cast (Nat.pow_pos (show 0 < b by omega)).ne'), logb_nat_power hb]

/-- A positive-length mantissa interval is contained in ([0,1)), with
the right endpoint permitted to equal one. -/
theorem log_interval_endpoints {b u d : Nat} (hb : 1 < b)
    (hlo : b ^ d ≤ u) (hhi : u < b ^ (d + 1)) :
    0 ≤ logb (b : ℝ) u - d ∧ logb (b : ℝ) u - d < logb (b : ℝ) (u + 1) - d ∧
      logb (b : ℝ) (u + 1) - d ≤ 1 := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hpos : 0 < b ^ d := Nat.pow_pos (by omega)
  have hu : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have h1 := logb_le_logb_of_le hbR
    (show (0 : ℝ) < ((b ^ d : Nat) : ℝ) by exact_mod_cast hpos)
    (show (((b ^ d : Nat) : ℝ)) ≤ u by exact_mod_cast hlo)
  rw [logb_nat_power hb] at h1
  have h2 := logb_lt_logb hbR hu (show (u : ℝ) < u + 1 by linarith)
  have h3 := logb_le_logb_of_le hbR (show (0 : ℝ) < u + 1 by linarith)
    (show (u : ℝ) + 1 ≤ ((b ^ (d + 1) : Nat) : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hhi))
  rw [logb_nat_power hb, Nat.cast_succ] at h3
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The fractional-log criterion in the proof of `lem:lead`.
Here (d) is one less than the number of digits in the desired prefix. -/
theorem prefix_iff_fractional_log {b u d n : Nat} (hb : 1 < b)
    (hlo : b ^ d ≤ u) (hhi : u < b ^ (d + 1)) (hn : b ^ d ≤ n) :
    (digits b u).reverse <+: (digits b n).reverse ↔
      Int.fract (logb (b : ℝ) n) ∈ Set.Ico (logb (b : ℝ) u - d)
        (logb (b : ℝ) (u + 1) - d) := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hpow : 0 < b ^ d := Nat.pow_pos (by omega)
  have huNat : 0 < u := by omega
  have hu : (0 : ℝ) < u := by exact_mod_cast huNat
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let L := logb (b : ℝ) n
  have hnLog := logb_le_logb_of_le hbR
    (show (0 : ℝ) < ((b ^ d : Nat) : ℝ) by exact_mod_cast hpow)
    (show ((b ^ d : Nat) : ℝ) ≤ n by exact_mod_cast hn)
  rw [logb_nat_power hb] at hnLog
  have hscaled (p : Nat) :
      (u * b ^ p ≤ n ∧ n < (u + 1) * b ^ p) ↔
      logb (b : ℝ) u + p ≤ L ∧ L < logb (b : ℝ) (u + 1) + p := by
    have hbp : 0 < b ^ p := Nat.pow_pos (by omega)
    have h1 : (0 : ℝ) < ((u * b ^ p : Nat) : ℝ) := by exact_mod_cast Nat.mul_pos huNat hbp
    have h2 : (0 : ℝ) < (((u + 1) * b ^ p : Nat) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.zero_lt_succ u) hbp
    have hleft := logb_le_logb hbR h1 hnR
    have hright := logb_lt_logb_iff hbR hnR h2
    rw [logb_scaled_nat hb huNat] at hleft
    rw [logb_scaled_nat hb (Nat.zero_lt_succ u), Nat.cast_succ] at hright
    exact ⟨fun h => ⟨hleft.2 (by exact_mod_cast h.1), hright.2 (by exact_mod_cast h.2)⟩,
      fun h => ⟨by exact_mod_cast hleft.1 h.1, by exact_mod_cast hright.1 h.2⟩⟩
  have ⟨hα, _, hβ⟩ := log_interval_endpoints hb hlo hhi
  rw [leading_prefix_iff_scaled_interval hb]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨ha, hz⟩ := (hscaled p).1 hp
    have hf : ⌊L⌋ = (d : ℤ) + p := Int.floor_eq_iff.mpr (by
      push_cast
      constructor <;> linarith)
    change logb (b : ℝ) u - d ≤ Int.fract L ∧ Int.fract L < logb (b : ℝ) (u + 1) - d
    rw [Int.fract, hf]
    push_cast
    exact ⟨by linarith, by linarith⟩
  · intro hp
    have hfloor : (d : ℤ) ≤ ⌊L⌋ := Int.le_floor.mpr (by simpa [L] using hnLog)
    let p := (⌊L⌋ - (d : ℤ)).toNat
    have hpz : (p : ℤ) = ⌊L⌋ - (d : ℤ) := Int.toNat_of_nonneg (sub_nonneg.mpr hfloor)
    have hpc : (p : ℝ) = (⌊L⌋ : ℝ) - d := by exact_mod_cast hpz
    refine ⟨p, (hscaled p).2 ?_⟩
    change logb (b : ℝ) u - d ≤ Int.fract L ∧ Int.fract L < logb (b : ℝ) (u + 1) - d at hp
    rw [Int.fract] at hp
    constructor <;> linarith [hp.1, hp.2]

/-- The precise interval-visiting consequence of the equidistribution
lemma `lem:logfact` that is used by `lem:lead`. -/
def FractionalLogHits (b : Nat) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ 1 → ∀ minimum : Nat, ∃ n ≥ minimum,
    Int.fract (logb (b : ℝ) (factorial (n + 1))) ∈ Set.Ico α β

/-- Lemma `lem:lead` follows from the interval-visiting consequence of
`lem:logfact` by its stated logarithmic criterion. -/
theorem leading_prefixes_of_fractional_logs {b : Nat} (hb : 1 < b)
    (hits : FractionalLogHits b) : LeadingPrefixes b := by
  intro a tail ha hd minimum
  obtain ⟨u, hu, hword⟩ := encode_leading_digits hb ha tail hd
  let d := (digits b u).length - 1
  have ⟨hlo, hhi⟩ := digits_power_bounds hb u hu
  have hlen := digits_length_positive hb hu
  have hhi' : u < b ^ (d + 1) := by
    have h : d + 1 = (digits b u).length := by dsimp [d]; omega
    simpa only [h] using hhi
  obtain ⟨hα, hab, hβ⟩ := log_interval_endpoints hb hlo hhi'
  obtain ⟨n, hn, hhit⟩ := hits _ _ hα hab hβ (max minimum (b ^ d))
  have hnp : b ^ d ≤ factorial (n + 1) := by
    have := factorial_ge (n + 1)
    omega
  refine ⟨n, by omega, ?_⟩
  rw [← hword]
  exact (prefix_iff_fractional_log hb hlo hhi' hnp).2 hhit

/-- The proportion of the first `N` fractional parts in the interval. -/
noncomputable def fractionalFrequency (x : Nat → ℝ) (α β : ℝ) (N : Nat) : ℝ := by
  classical
  exact ((Finset.range N).filter (fun n => Int.fract (x n) ∈ Set.Ico α β)).card / (N : ℝ)

/-- Index zero corresponds to (1!\), as in the sequence in the thesis. -/
noncomputable def fractionalLogFrequency (b : Nat) (α β : ℝ) (N : Nat) : ℝ :=
  fractionalFrequency (fun n => logb (b : ℝ) (factorial (n + 1))) α β N

/-- Uniform distribution modulo one in the interval-frequency form. -/
def Equidistributed (x : Nat → ℝ) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ 1 →
    Tendsto (fractionalFrequency x α β) atTop (𝓝 (β - α))

def FractionalLogsEquidistributed (b : Nat) : Prop :=
  Equidistributed fun n => logb (b : ℝ) (factorial (n + 1))

/-- A positive limiting proportion forces occurrences beyond every finite index,
as in the last step of `lem:logfact`. -/
theorem hits_of_equidistributed {x : Nat → ℝ} (h : Equidistributed x)
    {α β : ℝ} (hα : 0 ≤ α) (hab : α < β) (hβ : β ≤ 1) (minimum : Nat) :
    ∃ n ≥ minimum, Int.fract (x n) ∈ Set.Ico α β := by
  classical
  by_contra hnone
  have hbound (N : Nat) : fractionalFrequency x α β N ≤ (minimum : ℝ) / N := by
    unfold fractionalFrequency
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (show ((Finset.range N).filter (fun n =>
        Int.fract (x n) ∈ Set.Ico α β)).card ≤ minimum from by
      rw [← Finset.card_range minimum]
      apply Finset.card_le_card
      intro n hn
      have hvisit := (Finset.mem_filter.mp hn).2
      apply Finset.mem_range.mpr
      by_contra hn'
      exact hnone ⟨n, by omega, hvisit⟩)
  let mid := (β - α) / 2
  have hm0 : 0 < mid := by dsimp [mid]; linarith
  have hm1 : mid < β - α := by dsimp [mid]; linarith
  have hlt : ∀ᶠ N in atTop, mid < fractionalFrequency x α β N :=
    (h α β hα hab hβ).eventually (lt_mem_nhds hm1)
  have hgt : ∀ᶠ N : Nat in atTop, (minimum : ℝ) / N < mid :=
    (tendsto_const_div_atTop_nhds_zero_nat (minimum : ℝ)).eventually (gt_mem_nhds hm0)
  have habs : ∀ᶠ N : Nat in atTop, False := by
    filter_upwards [hlt, hgt] with N hl hh
    exact (not_lt_of_ge (hbound N)) (hh.trans hl)
  obtain ⟨_, hf⟩ := habs.exists
  exact hf

theorem fractionalLogHits_of_equidistributed {b : Nat}
    (h : FractionalLogsEquidistributed b) : FractionalLogHits b :=
  fun _ _ hα hab hβ minimum => hits_of_equidistributed h hα hab hβ minimum

/-- The assertion `mainthm01`, leaving only the equidistribution proof of
`lem:logfact` as a premise. -/
theorem full_complexities_of_log_distribution {b : Nat} (hb : 1 < b)
    (h : FractionalLogsEquidistributed b) (k : Nat) :
    ∃ words : List (List Nat), words.Nodup ∧ words.length = b ^ k ∧
      (∀ w, w ∈ words ↔ w.length = k ∧ Factor b w) ∧
      (∀ w, w ∈ words ↔ w.length = k ∧ ArithmeticFactor b w) :=
  full_complexities_of_leading_prefixes hb
    (leading_prefixes_of_fractional_logs hb (fractionalLogHits_of_equidistributed h)) k

end Thesis.FactorialWord
