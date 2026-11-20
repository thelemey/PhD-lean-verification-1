import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open Filter Topology

namespace Thesis.SturmianDensity

/-- The continued-fraction data used immediately after Fischler's formula.
The entry `t (k + 1)` is the reversed fraction whose first partial
quotient is `a k`. The closed interval includes the initial boundary
values without changing the argument about the limit. -/
structure ReversedFractions where
  a : Nat → Nat
  t : Nat → ℝ
  a_pos : ∀ k, 0 < a k
  t_bounds : ∀ k, 0 ≤ t k ∧ t k ≤ 1
  step : ∀ k, t (k + 1) = 1 / ((a k : ℝ) + t k)

private noncomputable def reversedValue (a : Nat → Nat) : Nat → ℝ
  | 0 => 0
  | k + 1 => 1 / ((a k : ℝ) + reversedValue a k)

private theorem reversedValue_bounds {a : Nat → Nat} (ha : ∀ k, 0 < a k) (k : Nat) :
    0 ≤ reversedValue a k ∧ reversedValue a k ≤ 1 := by
  induction k with
  | zero => simp [reversedValue]
  | succ k ih =>
    have h : (1 : ℝ) ≤ a k := by exact_mod_cast ha k
    have hden : (1 : ℝ) ≤ (a k : ℝ) + reversedValue a k := by linarith [ih.1]
    rw [reversedValue]
    exact ⟨div_nonneg zero_le_one (zero_le_one.trans hden), (div_le_one
      (zero_lt_one.trans_le hden)).2 hden⟩

/-- The reversed finite continued fractions [0; aₖ, …, a₁] of a sequence
of positive quotients, with t₀ = 0. -/
noncomputable def ReversedFractions.ofQuotients (a : Nat → Nat) (ha : ∀ k, 0 < a k) :
    ReversedFractions where
  a := a
  t := reversedValue a
  a_pos := ha
  t_bounds := reversedValue_bounds ha
  step _ := rfl

def ReversedFractions.BoundedQuotients (s : ReversedFractions) : Prop :=
  ∃ A : Nat, ∀ k, s.a k ≤ A

noncomputable def ReversedFractions.peak (s : ReversedFractions) (k : Nat) : ℝ :=
  1 + 1 / (1 + s.t (k + 1))

/-- The value supplied by the cited Fischler formula. -/
noncomputable def ReversedFractions.fischlerDensity (s : ReversedFractions) : ℝ :=
  1 / limsup s.peak atTop

private theorem tail_bounds (s : ReversedFractions) (k : Nat) :
    1 / ((s.a k : ℝ) + 1) ≤ s.t (k + 1) ∧ s.t (k + 1) ≤ 1 / (s.a k : ℝ) := by
  have ha : (0 : ℝ) < s.a k := by exact_mod_cast s.a_pos k
  obtain ⟨ht0, ht1⟩ := s.t_bounds k
  rw [s.step]
  exact ⟨one_div_le_one_div_of_le (by linarith) (by linarith),
    one_div_le_one_div_of_le ha (by linarith)⟩

private theorem peak_bounds (s : ReversedFractions) (k : Nat) :
    1 ≤ s.peak k ∧ s.peak k < 2 := by
  have ht : 0 < s.t (k + 1) := by
    rw [s.step]
    exact one_div_pos.mpr (add_pos_of_pos_of_nonneg
      (by exact_mod_cast s.a_pos k) (s.t_bounds k).1)
  unfold ReversedFractions.peak
  have h := one_div_lt_one_div_of_lt (a := (1 : ℝ)) zero_lt_one
    (show 1 < 1 + s.t (k + 1) by linarith)
  have hp := one_div_pos.mpr (show 0 < 1 + s.t (k + 1) by linarith)
  have hlt : 1 / (1 + s.t (k + 1)) < 1 := h.trans_eq one_div_one
  exact ⟨by linarith, by linarith⟩

private theorem peak_bounded (s : ReversedFractions) :
    IsBoundedUnder (· ≤ ·) atTop s.peak :=
  isBoundedUnder_of_eventually_le (Eventually.of_forall fun k => (peak_bounds s k).2.le)

private theorem peak_cobounded (s : ReversedFractions) :
    IsCoboundedUnder (· ≤ ·) atTop s.peak :=
  isCoboundedUnder_le_of_le atTop (fun k => (peak_bounds s k).1)

private theorem peak_limsup_ge_one (s : ReversedFractions) : 1 ≤ limsup s.peak atTop :=
  le_limsup_of_frequently_le (Eventually.of_forall fun k => (peak_bounds s k).1).frequently
    (peak_bounded s)

private theorem large_digit_in_tail (s : ReversedFractions) (hu : ¬ s.BoundedQuotients)
    (K A : Nat) : ∃ k ≥ K, A ≤ s.a k := by
  classical
  let B := max A ((Finset.range K).sup s.a)
  have h : ∃ k, B < s.a k := by
    by_contra hn
    apply hu
    refine ⟨B, ?_⟩
    intro k
    by_contra hk
    exact hn ⟨k, Nat.lt_of_not_ge hk⟩
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_, (Nat.le_max_left _ _).trans hk.le⟩
  by_contra hK
  have he : s.a k ≤ (Finset.range K).sup s.a :=
    Finset.le_sup (Finset.mem_range.mpr (Nat.lt_of_not_ge hK))
  exact (not_lt_of_ge (he.trans (Nat.le_max_right _ _))) hk

private noncomputable def highDigitIndex (s : ReversedFractions) (hu : ¬ s.BoundedQuotients) :
    Nat → Nat
  | 0 => (large_digit_in_tail s hu 0 0).choose
  | n + 1 => (large_digit_in_tail s hu (highDigitIndex s hu n + 1) (n + 1)).choose

private theorem highDigitIndex_strict (s : ReversedFractions) (hu : ¬ s.BoundedQuotients) :
    StrictMono (highDigitIndex s hu) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (large_digit_in_tail s hu (highDigitIndex s hu n + 1) (n + 1)).choose_spec.1

private theorem highDigitIndex_large (s : ReversedFractions) (hu : ¬ s.BoundedQuotients)
    (n : Nat) : n ≤ s.a (highDigitIndex s hu n) := by
  cases n with
  | zero => simp
  | succ n => exact (large_digit_in_tail s hu (highDigitIndex s hu n + 1) (n + 1)).choose_spec.2

/-- The unbounded-quotient part of `prop:dichotomy`. As in the text,
a subsequence of the partial quotients tends to infinity, the reversed
fractions tend to zero on it, and the peaks tend to two. -/
theorem peak_limsup_unbounded (s : ReversedFractions) (hu : ¬ s.BoundedQuotients) :
    limsup s.peak atTop = 2 := by
  let I := highDigitIndex s hu
  have htail : Tendsto (fun n => s.t (I n + 1)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => (s.t_bounds (I n + 1)).1) _
      tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply (tail_bounds s (I n)).2.trans
    exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast highDigitIndex_large s hu n)
  have hsub : Tendsto (fun n => s.peak (I n)) atTop (𝓝 2) := by
    have h := ((htail.const_add (1 : ℝ)).inv₀ (by norm_num)).const_add (1 : ℝ)
    convert h using 1
    · simp [ReversedFractions.peak, one_div]
    · norm_num
  apply le_antisymm
  · exact limsup_le_of_le (peak_cobounded s) (Eventually.of_forall fun k => (peak_bounds s k).2.le)
  · apply le_limsup_of_le (peak_bounded s)
    intro b hb
    exact le_of_tendsto hsub ((highDigitIndex_strict s hu).tendsto_atTop.eventually hb)

/-- The bounded-quotient upper bound on the limsup in `prop:dichotomy`. -/
theorem peak_limsup_bounded (s : ReversedFractions) (A : Nat) (hA : ∀ k, s.a k ≤ A) :
    limsup s.peak atTop ≤ (2 * (A : ℝ) + 3) / ((A : ℝ) + 2) := by
  apply limsup_le_of_le (peak_cobounded s)
  apply Eventually.of_forall
  intro k
  have hA1 : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have ha : (s.a k : ℝ) ≤ A := by exact_mod_cast hA k
  have ha1 : (0 : ℝ) < (s.a k : ℝ) + 1 := by positivity
  have htail : 1 / ((A : ℝ) + 1) ≤ s.t (k + 1) :=
    (one_div_le_one_div_of_le ha1 (by linarith)).trans (tail_bounds s k).1
  calc
    s.peak k ≤ 1 + 1 / (1 + 1 / ((A : ℝ) + 1)) := by
      unfold ReversedFractions.peak
      exact add_le_add_left (one_div_le_one_div_of_le (by positivity) (by linarith)) _
    _ = _ := by field_simp; ring

theorem density_unbounded (s : ReversedFractions) (hu : ¬ s.BoundedQuotients) :
    s.fischlerDensity = 1 / 2 := by rw [ReversedFractions.fischlerDensity, peak_limsup_unbounded s hu]

/-- The explicit strict lower bound for bounded partial quotients. -/
theorem density_bounded (s : ReversedFractions) (A : Nat) (hA : ∀ k, s.a k ≤ A) :
    ((A : ℝ) + 2) / (2 * (A : ℝ) + 3) ≤ s.fischlerDensity ∧
      (1 : ℝ) / 2 < ((A : ℝ) + 2) / (2 * (A : ℝ) + 3) := by
  have hp : 0 < limsup s.peak atTop := zero_lt_one.trans_le (peak_limsup_ge_one s)
  constructor
  · unfold ReversedFractions.fischlerDensity
    rw [← one_div_div]
    exact one_div_le_one_div_of_le hp (peak_limsup_bounded s A hA)
  · apply (div_lt_div_iff₀ (by norm_num) (by positivity)).2
    linarith

/-- The final equivalence of the dichotomy, at the level of the cited
Fischler formula. -/
theorem density_gt_half_iff (s : ReversedFractions) :
    (1 : ℝ) / 2 < s.fischlerDensity ↔ s.BoundedQuotients := by
  classical
  constructor
  · intro h
    by_contra hn
    rw [density_unbounded s hn] at h
    exact (lt_irrefl _ h)
  · rintro ⟨A, hA⟩
    obtain ⟨hl, hs⟩ := density_bounded s A hA
    exact hs.trans_le hl

/-- The lower bound and the equality case of `cor:palSturm` (1). -/
theorem half_le_density (s : ReversedFractions) : (1 : ℝ) / 2 ≤ s.fischlerDensity := by
  classical
  by_cases hb : s.BoundedQuotients
  · exact ((density_gt_half_iff s).2 hb).le
  · rw [density_unbounded s hb]

theorem density_eq_half_iff (s : ReversedFractions) :
    s.fischlerDensity = 1 / 2 ↔ ¬ s.BoundedQuotients := by
  refine ⟨fun he hb => ?_, density_unbounded s⟩
  have h := (density_gt_half_iff s).2 hb
  rw [he] at h
  exact (lt_irrefl _ h)

/-- Rational approximations to the slope are uniformly bounded away
at scale 1/q². -/
def BadlyApproximable (slope : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
    c / (q : ℝ) ^ 2 ≤ |slope - (p : ℝ) / (q : ℝ)|

/-- The conclusion of `prop:dichotomy` for a density whose value is
given by Fischler, with the classical bounded-quotient criterion stated
explicitly for the slope in question. -/
theorem density_gt_half_iff_badly_approximable (s : ReversedFractions) (slope density : ℝ)
    (hFischler : density = s.fischlerDensity)
    (hDiophantine : s.BoundedQuotients ↔ BadlyApproximable slope) :
    1 / 2 < density ↔ BadlyApproximable slope := by
  rw [hFischler, density_gt_half_iff s, hDiophantine]

end Thesis.SturmianDensity
