import Thesis.ThueMorse

namespace Thesis.ThueMorse

private theorem digitSum_maximal_digits {b : Nat} (hb : 1 < b) (e : Nat) :
    digitSum b (b ^ e - 1) = (b - 1) * e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hp : 0 < b ^ e := Nat.pow_pos (by omega)
    have he : b ^ (e + 1) - 1 = b * (b ^ e - 1) + (b - 1) := by
      rw [Nat.pow_succ', Nat.mul_sub, Nat.mul_one]
      have hle : b ≤ b * b ^ e := by
        simpa using Nat.mul_le_mul_left b (show 1 ≤ b ^ e by omega)
      omega
    rw [he, digitSum_block hb _ _ (by omega), ih, Nat.mul_succ]

private theorem digitSum_power_of_base {b : Nat} (hb : 1 < b) (e : Nat) :
    digitSum b (b ^ e) = 1 := by
  induction e with
  | zero => simpa using digitSum_block hb 0 1 hb
  | succ e ih =>
    rw [Nat.pow_succ']
    simpa using (digitSum_block hb (b ^ e) 0 (show 0 < b by omega)).trans (by simpa using ih)

private theorem word_step_no_carry {b N q r m j : Nat} (hb : 1 < b)
    (hr : r + m < b) (hj : m % N = j % N) :
    word b N (b * q + r + m) = (word b N (b * q + r) + j) % N := by
  simp only [Nat.add_assoc, word, digitSum_block hb q (r + m) hr,
    digitSum_block hb q r (by omega : r < b), Nat.mod_add_mod]
  simp only [← Nat.add_assoc]
  calc
    _ = (digitSum b q + r + m % N) % N := (Nat.add_mod_mod _ _ _).symm
    _ = (digitSum b q + r + j % N) % N := by rw [hj]
    _ = _ := Nat.add_mod_mod _ _ _

private theorem cancel_mod_add {N a c : Nat} (hN : 0 < N) (d : Nat)
    (h : (a + d) % N = (c + d) % N) : a % N = c % N := by
  have he := congrArg (fun x : Nat => (x + (N - d % N)) % N) h
  have hd' : d % N ≤ N := Nat.le_of_lt (Nat.mod_lt _ hN)
  have hd : d % N + (N - d % N) = N := by omega
  rw [← Nat.add_mod_mod a d N, ← Nat.add_mod_mod c d N] at he
  simpa only [Nat.mod_add_mod, Nat.add_assoc, hd, Nat.add_mod_right] using he

private theorem word_step_carry {b N e r m j : Nat} (hb : 1 < b)
    (hN : 0 < N) (hr : r < b) (hm : m < b) (hc : b ≤ r + m)
    (hj : (j + (b - 1) * (e + 1)) % N = m % N) :
    word b N (b * (b ^ e - 1) + r + m) =
      (word b N (b * (b ^ e - 1) + r) + j) % N := by
  have hp : 0 < b ^ e := Nat.pow_pos (by omega)
  have hmove : b * (b ^ e - 1) + r + m = b * b ^ e + (r + m - b) := by
    rw [Nat.mul_sub, Nat.mul_one]
    have H : b ≤ b * b ^ e := by
      simpa using Nat.mul_le_mul_left b (show 1 ≤ b ^ e by omega)
    omega
  simp only [hmove, word, digitSum_block hb (b ^ e) _ (by omega : r + m - b < b),
    digitSum_block hb (b ^ e - 1) r hr, digitSum_power_of_base hb,
    digitSum_maximal_digits hb, Nat.mod_add_mod]
  have hbalance : (1 + (r + m - b)) + (b - 1) * (e + 1) = r + m + (b - 1) * e := by
    rw [Nat.mul_succ]
    omega
  apply cancel_mod_add hN ((b - 1) * (e + 1))
  rw [hbalance]
  have he : (b - 1) * e + r + j + (b - 1) * (e + 1) =
      (r + (b - 1) * e) + (j + (b - 1) * (e + 1)) := by ac_rfl
  rw [he, ← Nat.add_mod_mod _ (j + (b - 1) * (e + 1)) N, hj, Nat.add_mod_mod]
  congr 1
  ac_rfl

/-- The witness in step 2 of `tw:main`, with the length bound cleared of
division. A carry across a block of maximal digits contributes a multiple
of `N` by choosing that block to have length `N - 1`. -/
theorem repeat_of_length_bound {b N k j m : Nat} (hb : 1 < b) (hN : 0 < N)
    (hm : 0 < m) (hmb : m < b) (hj : m % N = j % N) (hlen : k * m ≤ 2 * b) :
    StrongRepeat b N k j := by
  let q := b ^ (N - 1) - 1
  have hp : 0 < b ^ (N - 1) := Nat.pow_pos (by omega)
  have hshift : b * q + b = b * (q + 1) := by rw [Nat.mul_succ]
  have hk : (k - 1) * m ≤ 2 * b - m := by
    cases k with
    | zero => simp
    | succ k =>
      rw [Nat.succ_mul] at hlen
      simp only [Nat.succ_sub_one]
      omega
  have hcarry : (j + (b - 1) * (N - 1 + 1)) % N = m % N := by
    rw [show N - 1 + 1 = N by omega, Nat.add_mul_mod_self_right, hj]
  refine ⟨b * q, m, hm, ?_⟩
  intro t ht
  by_cases ht' : t < b
  · by_cases hr : t + m < b
    · exact word_step_no_carry hb hr hj
    · exact word_step_carry hb hN ht' hmb (by omega) hcarry
  · have hrt : t - b + m < b := by omega
    have he : b * q + t = b * (q + 1) + (t - b) := by rw [← hshift]; omega
    rw [he]
    exact word_step_no_carry hb hrt hj

/-- Every twist has a strong square, as in step 0 of `tw:main`. -/
theorem twisted_square {b N : Nat} (hb : 1 < b) (hN : 0 < N) (j : Nat) :
    StrongRepeat b N 2 j := by
  let d := b - 1
  have hd : 0 < d := by dsimp [d]; omega
  let q := (j + N - 1) / d
  let m := (j + N - 1) % d + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hmb : m < b := by
    have h := Nat.mod_lt (j + N - 1) hd
    dsimp [m, d] at *
    omega
  have hdecomp : j + N = m + d * q := by
    have h := Nat.mod_add_div (j + N - 1) d
    dsimp [m, q]
    omega
  let E := N * (q + 1) - q
  have hmul : q + 1 ≤ N * (q + 1) := by
    simpa using Nat.mul_le_mul_right (q + 1) (show 1 ≤ N by omega)
  have hE : E - 1 + 1 = E := by dsimp [E]; omega
  have hEq : q + E = N * (q + 1) := by dsimp [E]; omega
  have hcarry : (j + (b - 1) * (E - 1 + 1)) % N = m % N := by
    change (j + d * (E - 1 + 1)) % N = m % N
    rw [hE]
    calc
      _ = (j + d * E + N) % N := by rw [Nat.add_mod_right]
      _ = (m + d * (q + E)) % N := by
        rw [Nat.mul_add, ← Nat.add_assoc, ← hdecomp]
        congr 1
        ac_rfl
      _ = _ := by
        rw [hEq, show d * (N * (q + 1)) = N * (d * (q + 1)) by ac_rfl,
          Nat.add_mul_mod_self_left]
  refine ⟨b * (b ^ (E - 1) - 1) + (b - m), m, hm, ?_⟩
  intro t ht
  simp only [Nat.reduceSub, Nat.one_mul] at ht
  simp only [Nat.add_assoc (b * (b ^ (E - 1) - 1)) (b - m) t]
  exact word_step_carry hb hN (by omega) hmb (by omega) hcarry

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

private theorem digit_step_no_carry {b x : Nat} (hb : 1 < b) (hr : x % b ≠ 0) :
    digitSum b x = digitSum b (x - 1) + 1 := by
  have hrb := Nat.mod_lt x (show 0 < b by omega)
  have hdecomp := block_decomposition b x
  have hp : x - 1 = b * (x / b) + (x % b - 1) := by omega
  calc
    digitSum b x = digitSum b (x / b) + x % b := by
      simpa only [hdecomp] using digitSum_block hb (x / b) (x % b) hrb
    _ = digitSum b (x - 1) + 1 := by
      rw [hp, digitSum_block hb _ _ (by omega : x % b - 1 < b)]
      omega

private theorem digit_zero_last {b q : Nat} (hb : 1 < b) :
    digitSum b (b * q) = digitSum b q := by
  simpa using digitSum_block hb q 0 (show 0 < b by omega)

private theorem digit_step_one_carry {b y : Nat} (hb : 1 < b) (hy : y % b ≠ 0) :
    digitSum b (b * y - 1) + 1 = digitSum b (b * y) + (b - 1) := by
  have hy0 : 0 < y := by
    by_cases h : y = 0
    · simp [h] at hy
    · omega
  have hmul : b * y = b * (y - 1) + b := by
    rw [← Nat.mul_succ]
    exact congrArg (b * ·) (by omega)
  have hpred : b * y - 1 = b * (y - 1) + (b - 1) := by omega
  rw [hpred, digitSum_block hb _ _ (by omega : b - 1 < b),
    digit_zero_last hb, digit_step_no_carry hb hy]
  omega

private theorem digit_window {b N j i m L : Nat} (h : Window b N j i m L)
    {t : Nat} (ht : t < L) :
    digitSum b (i + t + m) % N = (digitSum b (i + t) + j) % N := by
  simpa only [word, Nat.mod_add_mod] using h t ht

private theorem step_agreement {b N j i m L t : Nat} (h : Window b N j i m L)
    (ht : t + 1 < L) :
    (digitSum b (i + t + m + 1) + digitSum b (i + t)) % N =
      (digitSum b (i + t + m) + digitSum b (i + t + 1)) % N := by
  have h0 := digit_window h (show t < L by omega)
  have h1 := digit_window h ht
  simp only [← Nat.add_assoc] at h1
  rw [show i + t + 1 + m = i + t + m + 1 by omega] at h1
  calc
    _ = ((digitSum b (i + t + m + 1) % N) + digitSum b (i + t)) % N :=
      (Nat.mod_add_mod _ _ _).symm
    _ = (digitSum b (i + t + 1) + j + digitSum b (i + t)) % N := by
      rw [h1, Nat.mod_add_mod]
    _ = (digitSum b (i + t) + j + digitSum b (i + t + 1)) % N := by
      congr 1
      ac_rfl
    _ = _ := by rw [← Nat.mod_add_mod _ N _, ← h0, Nat.mod_add_mod]

/-- A transition across a multiple of the base but not its square
cannot occur within the comparison window of a reduced repeat. -/
private theorem no_single_carry_transition {b N j i m L t y : Nat}
    (hb : 1 < b) (hN : 0 < N) (haper : ¬ N ∣ b - 1) (hm : m % b ≠ 0)
    (h : Window b N j i m L) (ht : t + 1 < L) (hy : i + t + 1 = b * y) :
    y % b = 0 := by
  by_cases hq : y % b = 0
  · exact hq
  · exfalso
    have hmod : (i + t + m + 1) % b ≠ 0 := by
      rw [show i + t + m + 1 = i + t + 1 + m by omega, hy, Nat.mul_add_mod]
      exact hm
    have hnc := digit_step_no_carry hb hmod
    simp only [Nat.add_sub_cancel] at hnc
    have hc := digit_step_one_carry hb hq
    rw [← hy, Nat.add_sub_cancel] at hc
    have ha := step_agreement h ht
    rw [hnc] at ha
    have hadd : digitSum b (i + t + m) + 1 + digitSum b (i + t) =
        (b - 1) + (digitSum b (i + t + m) + digitSum b (i + t + 1)) := by omega
    rw [hadd] at ha
    have hz := cancel_mod_add (a := b - 1) (c := 0) hN _ (by simpa only [Nat.zero_add] using ha)
    exact haper (Nat.dvd_iff_mod_eq_zero.mpr (by simpa using hz))

private theorem reduced_window {b N j k : Nat} (hb : 1 < b) (hN : 0 < N)
    (m : Nat) (hm : 0 < m) (i : Nat) (h : Window b N j i m ((k - 1) * m)) :
    ∃ i' m', 0 < m' ∧ m' % b ≠ 0 ∧ Window b N j i' m' ((k - 1) * m') := by
  by_cases hd : m % b = 0
  · have hmd : b * (m / b) = m := by simpa [hd] using block_decomposition b m
    have hp : 0 < m / b := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz, Nat.mul_zero] at hmd
      omega
    apply reduced_window hb hN (m / b) hp (i / b)
    intro t ht
    have ht' : b * t < (k - 1) * m := by
      have hlt := Nat.mul_lt_mul_of_pos_left ht (show 0 < b by omega)
      calc
        _ < b * ((k - 1) * (m / b)) := hlt
        _ = (k - 1) * (b * (m / b)) := by ac_rfl
        _ = _ := by rw [hmd]
    have hr := Nat.mod_lt i (show 0 < b by omega)
    have h0 : i + b * t = b * (i / b + t) + i % b := by
      rw [Nat.mul_add]
      have := block_decomposition b i
      omega
    have h1 : i + b * t + m = b * (i / b + t + m / b) + i % b := by
      rw [Nat.mul_add, hmd]; omega
    have hw := digit_window h ht'
    rw [h1, h0, digitSum_block hb _ _ hr, digitSum_block hb _ _ hr] at hw
    unfold word
    rw [Nat.mod_add_mod]
    apply cancel_mod_add hN (i % b)
    simpa only [Nat.add_assoc, Nat.add_comm (i % b) j] using hw
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
    (hb : 1 < b) (hN : 0 < N) (hm : m < b) (hL : m < L)
    (h : Window b N j i m L) : m % N = j % N := by
  have hnoncarry (t q r : Nat) (ht : t < L) (he : i + t = b * q + r)
      (hr : r + m < b) : m % N = j % N := by
    have hh := digit_window h ht
    rw [he, Nat.add_assoc (b * q) r m,
      digitSum_block hb q (r + m) hr,
      digitSum_block hb q r (by omega : r < b)] at hh
    apply cancel_mod_add hN (digitSum b q + r)
    simpa only [Nat.add_comm m, Nat.add_comm j, Nat.add_assoc] using hh
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
  by_cases hdiv : (q + 1) % b = 0
  · exact hdiv
  · exfalso
    have hmove : i + t + m = b * (q + 1) + (r + m - b) := by
      rw [he, Nat.mul_succ]
      omega
    have hstep := digit_step_no_carry hb hdiv
    simp only [Nat.add_sub_cancel] at hstep
    have hsum : digitSum b (i + t + m) + (b - 1) = digitSum b (i + t) + m := by
      rw [hmove, he, digitSum_block hb q r hr,
        digitSum_block hb (q + 1) _ (by omega : r + m - b < b), hstep]
      omega
    have hwin := digit_window h ht
    have hmod : (digitSum b (i + t + m) + (b - 1)) % N =
        digitSum b (i + t + m) % N := by
      rw [hsum, ← Nat.add_mod_mod _ m N, hj, Nat.add_mod_mod, ← hwin]
    have hz := cancel_mod_add (a := b - 1) (c := 0) hN (digitSum b (i + t + m))
      (by simpa only [Nat.zero_add, Nat.add_comm (b - 1)] using hmod)
    exact haper (Nat.dvd_iff_mod_eq_zero.mpr (by simpa using hz))

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
    obtain ⟨i, m, hm, hmnd, hw⟩ := reduced_window hb hN m hm i hw
    have hlen := reduced_length_le hb hN haper hmnd hw
    have h2 := Nat.mul_le_mul_right m (show 2 ≤ k - 1 by omega)
    have hmb : m < b := by
      have hle : m ≤ b := by omega
      have hne : m ≠ b := by intro he; simp [he] at hmnd
      omega
    have hj := twist_eq_of_noncarry hb hN hmb (by omega) hw
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
