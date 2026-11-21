import Thesis.ThueMorseCarries
import Mathlib.Data.Int.GCD

namespace Thesis.ThueMorse

private theorem word_step_no_carry {b N q r m j : Nat} (hb : 1 < b)
    (hr : r + m < b) (hj : m % N = j % N) :
    word b N (b * q + r + m) = (word b N (b * q + r) + j) % N := by
  apply (word_step_iff_digitDelta _ _ _ _ _).2
  rw [digitDelta_small_no_carry hb hr]
  exact Int.natCast_modEq_iff.2 hj

private theorem word_step_carry {b N e r m j : Nat} (hb : 1 < b)
    (hr : r < b) (hm : m < b) (hc : b ≤ r + m)
    (hj : (j + (b - 1) * (e + 1)) % N = m % N) :
    word b N (b * (b ^ e - 1) + r + m) =
      (word b N (b * (b ^ e - 1) + r) + j) % N := by
  apply (word_step_iff_digitDelta _ _ _ _ _).2
  have hp : 0 < b ^ e := Nat.pow_pos (by omega)
  rw [digitDelta_small_carry hb hr hm hc, Nat.sub_add_cancel hp,
    multiplicity_pow_self (by omega : b ≠ 0) (by rw [Nat.isUnit_iff]; omega)]
  have h := Int.natCast_modEq_iff.2 (show j + (b - 1) * (e + 1) ≡ m [MOD N] from hj)
  push_cast [Nat.cast_sub (show 1 ≤ b by omega)] at h
  simpa only [add_comm (1 : ℤ) (e : ℤ), add_sub_cancel_right] using
    Int.ModEq.sub_right (((b : ℤ) - 1) * ((e : ℤ) + 1)) h.symm

/-- The witness in step 2 of `tw:main`, with the length bound cleared of
division. A carry across a block of maximal digits contributes a multiple
of `N` by choosing its length to be one less than the carry period. -/
theorem repeat_of_length_bound {b N k j m : Nat} (hb : 1 < b) (hN : 0 < N)
    (hm : 0 < m) (hmb : m < b) (hj : m % N = j % N) (hlen : k * m ≤ 2 * b) :
    StrongRepeat b N k j := by
  let g := N / N.gcd (b - 1)
  let q := b ^ (g - 1) - 1
  have hg : 0 < g := Nat.div_pos (Nat.le_of_dvd hN (Nat.gcd_dvd_left _ _))
    (Nat.gcd_pos_of_pos_left _ hN)
  have hshift : b * q + b = b * (q + 1) := by rw [Nat.mul_succ]
  have hk : (k - 1) * m ≤ 2 * b - m := by
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.succ_mul] at hlen
      simp only [Nat.succ_sub_one]
      omega
  have hcarry : (j + (b - 1) * (g - 1 + 1)) % N = m % N := by
    obtain ⟨t, ht⟩ := (carryPeriod_dvd_iff hN (b - 1) g).2 (dvd_refl g)
    rw [Nat.sub_add_cancel hg, ht, Nat.add_mul_mod_self_left, hj]
  refine ⟨b * q, m, hm, ?_⟩
  intro t ht
  by_cases ht' : t < b
  · by_cases hr : t + m < b
    · exact word_step_no_carry hb hr hj
    · exact word_step_carry hb ht' hmb (by omega) hcarry
  · have hrt : t - b + m < b := by omega
    have he : b * q + t = b * (q + 1) + (t - b) := by rw [← hshift]; omega
    rw [he]
    exact word_step_no_carry hb hrt hj

/-- Every twist has a strong square, using the representative modulo the
gcd and the carry congruence of step 0 in `tw:main`. -/
theorem twisted_square {b N : Nat} (hb : 1 < b) (hN : 0 < N) (j : Nat) :
    StrongRepeat b N 2 j := by
  let a := b - 1
  let d := N.gcd a
  have hd : 0 < d := Nat.gcd_pos_of_pos_left a hN
  have hda : d ≤ a := Nat.le_of_dvd (by dsimp [a]; omega) (Nat.gcd_dvd_right _ _)
  let q := (j + d - 1) / d
  let m := (j + d - 1) % d + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hmd : m ≤ d := by have h := Nat.mod_lt (j + d - 1) hd; dsimp [m]; omega
  have hmb : m < b := by dsimp [a] at hda; omega
  have hdq : j + d = m + d * q := by
    have h := Nat.mod_add_div (j + d - 1) d
    dsimp [m, q]
    omega
  let t₀ : ℤ := Nat.gcdB N a * (1 - (q : ℤ))
  have hdiff : (m : ℤ) - j = (d : ℤ) * (1 - (q : ℤ)) := by
    have hh := congrArg (fun n : Nat => (n : ℤ)) hdq
    push_cast at hh
    rw [mul_sub, mul_one]
    omega
  have hsol : (a : ℤ) * t₀ ≡ (m : ℤ) - j [ZMOD (N : ℤ)] := by
    apply Int.modEq_iff_dvd.2
    refine ⟨Nat.gcdA N a * (1 - (q : ℤ)), ?_⟩
    rw [hdiff, show (d : ℤ) = (N : ℤ) * Nat.gcdA N a + (a : ℤ) * Nat.gcdB N a from
      Nat.gcd_eq_gcd_ab N a]
    dsimp [t₀]
    ring
  let E : Nat := (t₀ % (N : ℤ)).toNat + N
  have hE : 0 < E := by dsimp [E]; omega
  have hcast : ((t₀ % (N : ℤ)).toNat : ℤ) = t₀ % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))
  have hEeq : (E : ℤ) ≡ t₀ [ZMOD (N : ℤ)] := by
    change ((E : ℤ) % (N : ℤ)) = t₀ % (N : ℤ)
    dsimp [E]
    rw [Nat.cast_add, hcast, Int.add_emod_right, Int.emod_emod]
  have hcarry : (j + a * (E - 1 + 1)) % N = m % N := by
    rw [Nat.sub_add_cancel hE]
    apply Int.natCast_modEq_iff.1
    push_cast
    have hh := ((hEeq.mul_left (a : ℤ)).trans hsol).add_left (j : ℤ)
    have he : (j : ℤ) + ((m : ℤ) - j) = m := by ring
    simpa only [he] using hh
  refine ⟨b * (b ^ (E - 1) - 1) + (b - m), m, hm, ?_⟩
  intro t ht
  simp only [Nat.reduceSub, Nat.one_mul] at ht
  simp only [Nat.add_assoc (b * (b ^ (E - 1) - 1)) (b - m) t]
  exact word_step_carry hb (by omega) hmb (by omega) hcarry

/-- The positive representative `j'` used in `tw:main`. -/
def positiveTwist (N j : Nat) : Nat :=
  if j % N = 0 then N else j % N

/-- The existence direction of `tw:main`(ii), for every admissible twist. -/
theorem repeat_of_critical_bound {b N k j : Nat} (hb : 1 < b) (hN : 0 < N)
    (hk : 2 ≤ k) (hlen : k ≤ max 2 (2 * b / positiveTwist N j)) :
    StrongRepeat b N k j := by
  by_cases he : k = 2
  · subst k
    exact twisted_square hb hN j
  · have hm : 0 < positiveTwist N j := by
      unfold positiveTwist
      split <;> omega
    have hj : positiveTwist N j % N = j % N := by
      unfold positiveTwist
      split <;> simp_all
    have hbound : k ≤ 2 * b / positiveTwist N j := by omega
    have hmul : k * positiveTwist N j ≤ 2 * b :=
      (Nat.le_div_iff_mul_le hm).1 hbound
    have h3 := Nat.mul_le_mul_right (positiveTwist N j) (show 3 ≤ k by omega)
    exact repeat_of_length_bound hb hN hm (by omega) hj hmul

private def Window (b N j i m L : Nat) : Prop :=
  ∀ t < L, word b N (i + t + m) = (word b N (i + t) + j) % N

private theorem block_decomposition (b n : Nat) :
    b * (n / b) + n % b = n := by
  rw [Nat.add_comm, Nat.mod_add_div]

/-- Every multiple of the base in the transition window must also be
a multiple of its square, by the carry-period congruence in step 1. -/
private theorem no_single_carry_transition {b N j i m L t y : Nat}
    (hb : 1 < b) (hN : 0 < N) (haper : ¬ N ∣ b - 1) (hm : m % b ≠ 0)
    (h : Window b N j i m L) (ht : t + 1 < L) (hy : i + t + 1 = b * y) :
    y % b = 0 := by
  have hz : ¬ b ∣ i + t + m + 1 := by
    rw [show i + t + m + 1 = i + t + 1 + m by omega, hy, Nat.dvd_iff_mod_eq_zero, Nat.mul_add_mod]
    exact hm
  have h0 := (word_step_iff_digitDelta b N (i + t) m j).1 (h t (by omega))
  have h1 := (word_step_iff_digitDelta b N (i + t + 1) m j).1 (by
    simpa only [Nat.add_assoc] using h (t + 1) ht)
  have hc := h1.sub h0
  rw [digitDelta_succ_sub hb, sub_self, multiplicity_eq_zero.2 hz, Nat.cast_zero, zero_sub,
    neg_mul_neg] at hc
  have hmod : (b - 1) * multiplicity b (i + t + 1) ≡ 0 [MOD N] := by
    apply Int.natCast_modEq_iff.1
    simpa only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ b by omega), Nat.cast_one, Nat.cast_zero] using hc
  have hd := (carryPeriod_dvd_iff hN (b - 1) _).1 (Nat.modEq_zero_iff_dvd.1 hmod)
  have hpos : 0 < multiplicity b (i + t + 1) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact (multiplicity_eq_zero.1 hzero) ⟨y, hy⟩
  have ht₂ := (two_le_carryPeriod hN haper).trans (Nat.le_of_dvd hpos hd)
  have hf : FiniteMultiplicity b (i + t + 1) := Nat.finiteMultiplicity_iff.2 ⟨by omega, by omega⟩
  have hsq := hf.pow_dvd_iff_le_multiplicity.2 ht₂
  rw [hy, pow_succ', Nat.mul_dvd_mul_iff_left (show 0 < b by omega), pow_one] at hsq
  exact Nat.dvd_iff_mod_eq_zero.1 hsq

private theorem reduced_window {b N j k : Nat} (hb : 1 < b)
    (m : Nat) (hm : 0 < m) (i : Nat) (h : Window b N j i m ((k - 1) * m)) :
    ∃ i' m', 0 < m' ∧ m' % b ≠ 0 ∧ Window b N j i' m' ((k - 1) * m') := by
  by_cases hd : m % b = 0
  · have hmd : b * (m / b) = m := by simpa [hd] using block_decomposition b m
    have hp : 0 < m / b := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz, Nat.mul_zero] at hmd
      omega
    let q := if i % b = 0 then i / b else i / b + 1
    let lead := if i % b = 0 then 0 else b - i % b
    have hrem : i % b < b := Nat.mod_lt _ (by omega)
    have hdecomp := block_decomposition b i
    have hlead : lead < b := by dsimp [lead]; split <;> omega
    have hs : i + lead = b * q := by
      dsimp [lead, q]
      split
      · rename_i h
        simp at hdecomp ⊢
        omega
      · rw [Nat.mul_succ]
        omega
    apply reduced_window hb (m / b) hp q
    intro t ht
    have ht' : lead + b * t < (k - 1) * m := by
      have hle := Nat.mul_le_mul_left b (Nat.succ_le_of_lt ht)
      have hsize : b * ((k - 1) * (m / b)) = (k - 1) * m := calc
        _ = (k - 1) * (b * (m / b)) := by ac_rfl
        _ = _ := by rw [hmd]
      rw [Nat.mul_succ, hsize] at hle
      omega
    have hsample := (word_step_iff_digitDelta _ _ _ _ _).1 (h _ ht')
    have he : i + (lead + b * t) = b * (q + t) + 0 := by rw [Nat.mul_add]; omega
    rw [he, ← hmd, digitDelta_scale hb _ _ _ (by omega)] at hsample
    exact (word_step_iff_digitDelta _ _ _ _ _).2 hsample
  · exact ⟨i, m, hm, hd, h⟩
termination_by m
decreasing_by exact Nat.div_lt_self hm hb

private theorem next_multiple {b : Nat} (hb : 1 < b) (n : Nat) :
    ∃ t < b, ∃ y, n + t = b * y := by
  have hdecomp := block_decomposition b n
  have hmod := Nat.mod_lt n (show 0 < b by omega)
  by_cases hz : n % b = 0
  · exact ⟨0, by omega, n / b, by omega⟩
  · refine ⟨b - n % b, by omega, n / b + 1, ?_⟩
    rw [Nat.mul_succ]
    omega

private theorem not_both_divisible {b y : Nat} (hb : 1 < b)
    (hy : y % b = 0) : (y + 1) % b ≠ 0 := by
  rw [Nat.add_mod, hy, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hb]
  decide

private theorem reduced_length_le {b N j i m L : Nat} (hb : 1 < b)
    (hN : 0 < N) (haper : ¬ N ∣ b - 1) (hm : m % b ≠ 0)
    (h : Window b N j i m L) : L ≤ 2 * b := by
  by_cases hle : L ≤ 2 * b
  · exact hle
  · obtain ⟨t, ht, y, hy⟩ := next_multiple hb (i + 1)
    have hy' : i + (t + b) + 1 = b * (y + 1) := by rw [Nat.mul_succ]; omega
    have hz := no_single_carry_transition hb hN haper hm h (by omega)
      (show i + t + 1 = b * y by omega)
    have hz' := no_single_carry_transition hb hN haper hm h (by omega) hy'
    exact False.elim (not_both_divisible hb hz hz')

private theorem twist_eq_of_noncarry {b N j i m L : Nat}
    (hb : 1 < b) (hm : m < b) (hL : m < L)
    (h : Window b N j i m L) : m % N = j % N := by
  have hnoncarry (t q r : Nat) (ht : t < L) (he : i + t = b * q + r)
      (hr : r + m < b) : m % N = j % N := by
    have hh := (word_step_iff_digitDelta _ _ _ _ _).1 (h t ht)
    rw [he, digitDelta_small_no_carry hb hr] at hh
    exact Int.natCast_modEq_iff.1 hh
  by_cases hr : i % b + m < b
  · exact hnoncarry 0 (i / b) (i % b) (by omega)
      (by simpa using (block_decomposition b i).symm) hr
  · have hdecomp := block_decomposition b i
    refine hnoncarry (b - i % b) (i / b + 1) 0 (by omega) ?_ (by omega)
    rw [Nat.add_zero, Nat.mul_succ]
    have hmod := Nat.mod_lt i (show 0 < b by omega)
    omega

/-- A carry within a comparison window whose twist equals the block length
must pass a multiple of the base in the next digit as well. -/
private theorem no_single_carry_position {b N j i m L t q r : Nat}
    (hb : 1 < b) (hN : 0 < N) (haper : ¬ N ∣ b - 1)
    (hm : m < b) (hj : m % N = j % N) (h : Window b N j i m L)
    (ht : t < L) (he : i + t = b * q + r) (hr : r < b) (hc : b ≤ r + m) :
    (q + 1) % b = 0 := by
  have hwin := (word_step_iff_digitDelta b N (i + t) m j).1 (h t ht)
  rw [he, digitDelta_small_carry hb hr hm hc] at hwin
  have hmod := (Int.natCast_modEq_iff.2 hj).sub hwin
  have hz : (b - 1) * (1 + multiplicity b (q + 1)) ≡ 0 [MOD N] := by
    apply Int.natCast_modEq_iff.1
    push_cast [Nat.cast_sub (show 1 ≤ b by omega)]
    have he : (m : ℤ) - ((m : ℤ) - ((b : ℤ) - 1) * (1 + multiplicity b (q + 1))) =
        ((b : ℤ) - 1) * (1 + multiplicity b (q + 1)) := by ring
    simpa only [he, sub_self] using hmod
  have hd := (carryPeriod_dvd_iff hN (b - 1) _).1 (Nat.modEq_zero_iff_dvd.1 hz)
  have hh := (two_le_carryPeriod hN haper).trans (Nat.le_of_dvd (by omega) hd)
  have hf : FiniteMultiplicity b (q + 1) := Nat.finiteMultiplicity_iff.2 ⟨by omega, by omega⟩
  have hdiv := hf.pow_dvd_iff_le_multiplicity.2 (show 1 ≤ multiplicity b (q + 1) by omega)
  exact Nat.dvd_iff_mod_eq_zero.1 (by simpa using hdiv)

private theorem short_carry_window {b N j i m L : Nat}
    (hb : 1 < b) (hN : 0 < N) (haper : ¬ N ∣ b - 1)
    (hm : 0 < m) (hmb : m < b) (hj : m % N = j % N)
    (h : Window b N j i m L) : L ≤ 2 * b - m := by
  by_cases hle : L ≤ 2 * b - m
  · exact hle
  · let q := i / b
    let r := max (i % b) (b - m)
    let t := r - i % b
    have hdecomp := block_decomposition b i
    have hmod := Nat.mod_lt i (show 0 < b by omega)
    have hr : r < b := by dsimp [r]; omega
    have hc : b ≤ r + m := by dsimp [r]; omega
    have ht : t ≤ b - m := by dsimp [t, r]; omega
    have hpos : i + t = b * q + r := by dsimp [q, t, r]; omega
    have hpos' : i + (t + b) = b * (q + 1) + r := by rw [Nat.mul_succ]; omega
    have hz := no_single_carry_position hb hN haper hmb hj h (by omega) hpos hr hc
    have hz' := no_single_carry_position hb hN haper hmb hj h (by omega) hpos' hr hc
    exact False.elim (not_both_divisible hb hz hz')

/-- The upper bound in `tw:main`(ii), for nonperiodic digit-sum words. -/
theorem critical_bound_of_repeat {b N k j : Nat} (hb : 1 < b) (hN : 0 < N)
    (haper : ¬ N ∣ b - 1) (h : StrongRepeat b N k j) :
    k ≤ max 2 (2 * b / positiveTwist N j) := by
  by_cases hk : k ≤ 2
  · exact Nat.le_trans hk (Nat.le_max_left _ _)
  · obtain ⟨i, m, hm, hw⟩ := h
    obtain ⟨i, m, hm, hmnd, hw⟩ := reduced_window hb m hm i hw
    have hlen := reduced_length_le hb hN haper hmnd hw
    have h2 := Nat.mul_le_mul_right m (show 2 ≤ k - 1 by omega)
    have hmb : m < b := by
      have hle : m ≤ b := by omega
      have hne : m ≠ b := by intro he; simp [he] at hmnd
      omega
    have hj := twist_eq_of_noncarry hb hmb (by omega) hw
    have hs := short_carry_window hb hN haper hm hmb hj hw
    have hkm : k * m ≤ 2 * b := by
      have he : k * m = (k - 1) * m + m := by
        rw [← Nat.succ_mul]
        exact congrArg (· * m) (by omega)
      omega
    have htw : positiveTwist N j ≤ m := by
      unfold positiveTwist
      split
      · rename_i hz
        have hd : N ∣ m := Nat.dvd_iff_mod_eq_zero.mpr (hj.trans hz)
        exact Nat.le_of_dvd hm hd
      · exact Nat.le_trans (Nat.le_of_eq hj.symm) (Nat.mod_le _ _)
    have htw0 : 0 < positiveTwist N j := by unfold positiveTwist; split <;> omega
    apply Nat.le_trans _ (Nat.le_max_right _ _)
    apply (Nat.le_div_iff_mul_le htw0).2
    exact Nat.le_trans (Nat.mul_le_mul_left k htw) hkm

/-- The nonperiodic case of the twisted critical exponent theorem
`tw:main`. Natural twists represent all residues modulo `N`. -/
theorem twisted_critical_exponent {b N k j : Nat} (hb : 1 < b) (hN : 0 < N)
    (hk : 2 ≤ k) (haper : ¬ N ∣ b - 1) :
    StrongRepeat b N k j ↔ k ≤ max 2 (2 * b / positiveTwist N j) :=
  ⟨critical_bound_of_repeat hb hN haper, repeat_of_critical_bound hb hN hk⟩

end Thesis.ThueMorse
