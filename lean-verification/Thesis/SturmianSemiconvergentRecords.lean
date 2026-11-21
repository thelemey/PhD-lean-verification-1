import Thesis.SturmianConvergentErrors
import Thesis.RotationRecordEnumeration

open GenContFract Filter

namespace Thesis.SturmianDensity

private def bracketOfOppositeErrors {a : ℝ} (l u : Nat) (p q : ℤ)
    (hl : 0 < l) (hu : 0 < u) (hL : 0 < (l : ℝ) * a - p)
    (hU : 0 < (q : ℝ) - (u : ℝ) * a)
    (hdet : (l : ℤ) * q - (u : ℤ) * p = 1) : RotationRecordBracket a where
  lowerTime := l
  upperTime := u
  lowerIndex := p
  upperIndex := q
  lowerTime_pos := hl
  upperTime_pos := hu
  lower_pos := hL
  upper_pos := hU
  determinant := hdet
  width_le_one := by
    have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hd : (l : ℝ) * q - (u : ℝ) * p = 1 := by exact_mod_cast hdet
    have h₁ := mul_le_mul_of_nonneg_right huR hL.le
    have h₂ := mul_le_mul_of_nonneg_right hlR hU.le
    simp only [one_mul] at h₁ h₂
    have he : (u : ℝ) * ((l : ℝ) * a - p) + (l : ℝ) * ((q : ℝ) - (u : ℝ) * a) = 1 := by
      calc
        _ = (l : ℝ) * q - (u : ℝ) * p := by ring
        _ = _ := hd
    linarith

private theorem neg_one_pow_cases (k : Nat) : (-1 : ℝ) ^ k = 1 ∨ (-1 : ℝ) ^ k = -1 := by
  induction k with
  | zero => simp
  | succ k ih => rcases ih with h | h <;> simp [pow_succ, h]

/-- The lattice bracket just before each intermediate convergent in a
palindrome-length block. Its two times are the current convergent and
the preceding intermediate one, in the order dictated by the signs. -/
theorem exists_semiconvergent_bracket {a : ℝ} (ha : Irrational a) (k m : Nat)
    (hm : 1 ≤ m) (hm' : m ≤ (slopeFractions a ha).prefixBlocks.d k) :
    ∃ b : RotationRecordBracket a,
      b.nextTime = (slopeFractions a ha).prefixBlocks.len k m + 2 ∧
      max b.lowerTime b.upperTime =
        max ((slopeFractions a ha).prefixBlocks.Q (k + 1))
          ((m - 1) * (slopeFractions a ha).prefixBlocks.Q (k + 1) +
            (slopeFractions a ha).prefixBlocks.Q k) := by
  let s := (slopeFractions a ha).prefixBlocks
  let U := s.Q (k + 1)
  let V := s.Q k
  let g := GenContFract.of a
  let p : ℤ := ⌊(g.contsAux (k + 3)).a⌋
  let q : ℤ := ⌊(g.contsAux (k + 2)).a⌋
  let r := m - 1
  let W := r * U + V
  let z : ℤ := (r : ℤ) * p + q
  let A := convergentErrorMagnitude a (k + 2)
  let B := convergentErrorMagnitude a (k + 1) - (r : ℝ) * A
  have hA : 0 < A := convergentErrorMagnitude_pos ha (k + 2)
  have hB : 0 < B := by
    have hh := convergentErrorMagnitude_step ha (k + 1)
    change convergentErrorMagnitude a (k + 1) =
      (partialQuotient a (k + 2) : ℝ) * A + convergentErrorMagnitude a (k + 3) at hh
    have hr : r ≤ partialQuotient a (k + 2) := Nat.le_trans (Nat.sub_le _ _) hm'
    have hh' := mul_le_mul_of_nonneg_right (show (r : ℝ) ≤ partialQuotient a (k + 2) by
      exact_mod_cast hr) hA.le
    dsimp only [B]
    linarith [convergentErrorMagnitude_pos ha (k + 3)]
  have hp : (p : ℝ) = (g.contsAux (k + 3)).a := slope_contsAux_numerator_integer ha _
  have hq : (q : ℝ) = (g.contsAux (k + 2)).a := slope_contsAux_numerator_integer ha _
  have hU : (U : ℝ) = (g.contsAux (k + 3)).b := continuedDenominator_eq_contsAux ha _
  have hV : (V : ℝ) = (g.contsAux (k + 2)).b := continuedDenominator_eq_contsAux ha _
  have hU₀ : 0 < U := s.positive _
  have hV₀ : 0 < V := s.positive _
  have hW₀ : 0 < W := Nat.add_pos_right _ hV₀
  have heA : A = (-1 : ℝ) ^ (k + 2) * ((U : ℝ) * a - p) := by
    rw [hU, hp]
    rfl
  have heB : B = -((-1 : ℝ) ^ (k + 2)) * ((W : ℝ) * a - z) := by
    have hsign : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ (k + 2)) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    dsimp only [B, convergentErrorMagnitude]
    rw [hsign, heA]
    change -((-1 : ℝ) ^ (k + 2)) * convergentError a (k + 1) -
      (r : ℝ) * ((-1 : ℝ) ^ (k + 2) * ((U : ℝ) * a - p)) =
        -((-1 : ℝ) ^ (k + 2)) * ((W : ℝ) * a - z)
    have he : convergentError a (k + 1) = (V : ℝ) * a - q := by rw [hV, hq]; rfl
    rw [he]
    dsimp only [W, z]
    push_cast
    ring
  have hterm : ¬g.TerminatedAt (k + 2 - 1) := by
    intro hn
    obtain ⟨t, ht⟩ := (GenContFract.terminates_iff_rat a).1 ⟨_, hn⟩
    exact ha ⟨t, ht.symm⟩
  have hD : (U : ℝ) * q - (V : ℝ) * p = (-1 : ℝ) ^ (k + 2) := by
    rw [hU, hV, hp, hq]
    have h := (SimpContFract.of a).determinant_aux (n := k + 2) (Or.inr hterm)
    change (g.contsAux (k + 2)).a * (g.contsAux (k + 3)).b -
      (g.contsAux (k + 2)).b * (g.contsAux (k + 3)).a = (-1 : ℝ) ^ (k + 2) at h
    rw [mul_comm (g.contsAux (k + 3)).b]
    exact h
  have hdet : (U : ℝ) * z - (W : ℝ) * p = (-1 : ℝ) ^ (k + 2) := by
    dsimp only [W, z]
    push_cast
    calc
      _ = (U : ℝ) * q - (V : ℝ) * p := by ring
      _ = _ := hD
  have htime : U + W = s.len k m + 2 := by
    change U + (r * U + V) = m * U + V - 2 + 2
    have hmul : m * U = r * U + U := by
      have hmr : m = r + 1 := by dsimp [r]; omega
      rw [hmr, Nat.add_mul, Nat.one_mul]
    have ht : 2 ≤ U := s.Q_next_ge_two k
    omega
  rcases neg_one_pow_cases (k + 2) with h | h
  · rw [h] at heA heB hdet
    have hL : 0 < (U : ℝ) * a - p := by linarith
    have hR : 0 < (z : ℝ) - (W : ℝ) * a := by linarith
    have hdetI : (U : ℤ) * z - (W : ℤ) * p = 1 := by exact_mod_cast hdet
    exact ⟨bracketOfOppositeErrors U W p z hU₀ hW₀ hL hR hdetI, htime, rfl⟩
  · rw [h] at heA heB hdet
    have hL : 0 < (W : ℝ) * a - z := by linarith
    have hR : 0 < (p : ℝ) - (U : ℝ) * a := by linarith
    have hd : (W : ℝ) * p - (U : ℝ) * z = 1 := by linarith
    have hdetI : (W : ℤ) * p - (U : ℤ) * z = 1 := by exact_mod_cast hd
    refine ⟨bracketOfOppositeErrors W U z p hW₀ hU₀ hL hR hdetI, ?_, ?_⟩
    · exact (Nat.add_comm W U).trans htime
    · exact max_comm _ _

private theorem semiconvergent_cover (s : PalindromePrefixBlocks) {t : Nat} (ht : s.Q 1 < t) :
    ∃ k m, 1 ≤ m ∧ m ≤ s.d k ∧
      max (s.Q (k + 1)) ((m - 1) * s.Q (k + 1) + s.Q k) < t ∧ t ≤ s.len k m + 2 := by
  have hex : ∃ k, t ≤ s.Q (k + 2) := by
    obtain ⟨k, hk⟩ := (s.last_strictMono.tendsto_atTop.eventually_ge_atTop t).exists
    rw [s.last_eq] at hk
    exact ⟨k, by omega⟩
  let k := Nat.find hex
  have hk : t ≤ s.Q (k + 2) := Nat.find_spec hex
  have hprev : s.Q (k + 1) < t := by
    cases hk' : k with
    | zero => simpa [hk'] using ht
    | succ j =>
      have hj : j < k := by omega
      have h := Nat.lt_of_not_ge (Nat.find_min hex hj)
      simpa only [hk'] using h
  have hV : s.Q k < s.Q (k + 1) := s.increasing (Nat.lt_succ_self _)
  have hmex : ∃ m, t ≤ m * s.Q (k + 1) + s.Q k := by
    rw [s.step] at hk
    exact ⟨s.d k, hk⟩
  let m := Nat.find hmex
  have hm : t ≤ m * s.Q (k + 1) + s.Q k := Nat.find_spec hmex
  have hmp : 1 ≤ m := by
    by_contra hzero
    have he : m = 0 := by omega
    rw [he, zero_mul, zero_add] at hm
    omega
  have hml : m ≤ s.d k := Nat.find_min' hmex (s.step k ▸ hk)
  have hleft : (m - 1) * s.Q (k + 1) + s.Q k < t :=
    Nat.lt_of_not_ge (Nat.find_min hmex (by omega : m - 1 < m))
  refine ⟨k, m, hmp, hml, max_lt_iff.2 ⟨hprev, hleft⟩, ?_⟩
  unfold PalindromePrefixBlocks.len
  omega

/-- The long palindrome-prefix lengths of the actual characteristic
word are exactly the intermediate continuant lengths of the thesis. -/
theorem characteristic_palPrefix_iff_continuant_block {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) :
    let s := (slopeFractions a hirr).prefixBlocks
    ∀ L ≥ s.Q 1 - 1, PalPrefix (FactorTree.characteristicWord a) L ↔
      ∃ k m, 1 ≤ m ∧ m ≤ s.d k ∧ s.len k m = L := by
  intro s L hL
  have hs := characteristic_palPrefix_iff_fractional_record ha ha' hirr L
  change PalPrefix (FactorTree.characteristicWord a) L ↔ FractionalRecord a (L + 2) at hs
  rw [hs]
  constructor
  · intro h
    obtain ⟨k, m, hm, hm', hprev, hnext⟩ := semiconvergent_cover s (by omega : s.Q 1 < L + 2)
    obtain ⟨b, ht, hmax⟩ := exists_semiconvergent_bracket hirr k m hm hm'
    change b.nextTime = s.len k m + 2 at ht
    have he : L + 2 = s.len k m + 2 := by
      apply le_antisymm hnext
      by_contra hne
      apply b.not_record_between _ _ h
      · rwa [hmax]
      · rw [ht]; omega
    exact ⟨k, m, hm, hm', by omega⟩
  · rintro ⟨k, m, hm, hm', he⟩
    obtain ⟨b, ht, _⟩ := exists_semiconvergent_bracket hirr k m hm hm'
    change b.nextTime = s.len k m + 2 at ht
    rw [← he, ← ht]
    exact b.record_at_sum hirr

/-- The first quotient gives the last time in the initial run of records
whose fractional part is simply the time multiplied by the slope. -/
theorem first_partialQuotient_bounds {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) :
    (partialQuotient a 0 : ℝ) * a < 1 ∧ 1 < ((partialQuotient a 0 : ℝ) + 1) * a := by
  have hf : ⌊a⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨ha.le, ha'⟩
  have hfr : (IntFractPair.of a).fr = a := by simp [IntFractPair.of, Int.fract, hf]
  have hstream := IntFractPair.stream_succ_of_some (IntFractPair.stream_zero a)
    (show (IntFractPair.of a).fr ≠ 0 by rw [hfr]; exact ha.ne')
  rw [hfr] at hstream
  have hq : (partialQuotient a 0 : ℤ) = ⌊a⁻¹⌋ := by
    have h := IntFractPair.one_le_succ_nth_stream_b hstream
    have hnonneg : 0 ≤ ⌊a⁻¹⌋ := zero_le_one.trans h
    simp [partialQuotient, hstream, IntFractPair.of, Int.toNat_of_nonneg hnonneg]
  have ht : (partialQuotient a 0 : ℝ) < a⁻¹ := by
    have h := Int.floor_le a⁻¹
    rw [← hq] at h
    push_cast at h
    refine lt_of_le_of_ne h ?_
    exact fun he => (hirr.inv.ne_int (partialQuotient a 0)) (by exact_mod_cast he.symm)
  have hu : a⁻¹ < (partialQuotient a 0 : ℝ) + 1 := by
    have h := Int.lt_floor_add_one a⁻¹
    rw [← hq] at h
    exact_mod_cast h
  exact ⟨(lt_div_iff₀ ha).1 (by simpa only [one_div] using ht),
    (div_lt_iff₀ ha).1 (by simpa only [one_div] using hu)⟩

private theorem early_fractionalRecord {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) {t : Nat} (ht : t ≤ partialQuotient a 0) : FractionalRecord a t := by
  have hq := (first_partialQuotient_bounds ha ha' hirr).1
  have frac_eq (j : Nat) (hj : j ≤ partialQuotient a 0) :
      Int.fract ((j : ℝ) * a) = (j : ℝ) * a := by
    apply Int.fract_eq_self.2
    exact ⟨by positivity, (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) ha.le).trans_lt hq⟩
  right
  intro j _ hj
  rw [frac_eq j (hj.le.trans ht), frac_eq t ht]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hj) ha

private theorem exists_second_block_bracket {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) {m : Nat} (hm : 1 ≤ m) (hm' : m ≤ partialQuotient a 1) :
    ∃ b : RotationRecordBracket a,
      b.lowerTime = (m - 1) * partialQuotient a 0 + 1 ∧
      b.upperTime = partialQuotient a 0 ∧ b.nextTime = m * partialQuotient a 0 + 1 := by
  let A := partialQuotient a 0
  let r := m - 1
  have he := initial_convergentErrorMagnitudes ha ha' hirr
  have hrec := convergentErrorMagnitude_step hirr 0
  rw [he.1, he.2] at hrec
  have herr : 0 < 1 - (A : ℝ) * a := sub_pos.2 (first_partialQuotient_bounds ha ha' hirr).1
  have hr : (r : ℝ) ≤ partialQuotient a 1 := by exact_mod_cast (show r ≤ _ from (Nat.sub_le _ _).trans hm')
  have hp := mul_le_mul_of_nonneg_right hr herr.le
  have hlo : 0 < (((r * A + 1 : Nat) : ℝ) * a - (r : ℤ)) := by
    push_cast
    change a = (partialQuotient a 1 : ℝ) * (1 - (A : ℝ) * a) +
      convergentErrorMagnitude a 2 at hrec
    linarith [convergentErrorMagnitude_pos hirr 2]
  let b := bracketOfOppositeErrors (r * A + 1) A (r : ℤ) 1
    (by omega) (partialQuotient_pos hirr 0) hlo
    (by simpa using herr) (by push_cast; ring)
  refine ⟨b, rfl, rfl, ?_⟩
  change r * A + 1 + A = m * A + 1
  have hmr : m = r + 1 := by dsimp [r]; omega
  rw [hmr, Nat.add_mul, Nat.one_mul]
  ac_rfl

private theorem second_block_record_iff {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) {t : Nat} (ht : partialQuotient a 0 < t)
    (hT : t ≤ partialQuotient a 1 * partialQuotient a 0 + 1) :
    FractionalRecord a t ↔ ∃ m, 1 ≤ m ∧ m ≤ partialQuotient a 1 ∧
      m * partialQuotient a 0 + 1 = t := by
  constructor
  · intro hr
    have hex : ∃ m : Nat, t ≤ m * partialQuotient a 0 + 1 := ⟨_, hT⟩
    let m := Nat.find hex
    have hnext : t ≤ m * partialQuotient a 0 + 1 := Nat.find_spec hex
    have hpos : 1 ≤ m := by
      by_contra! h
      have : m = 0 := by omega
      rw [this, Nat.zero_mul, Nat.zero_add] at hnext
      have := partialQuotient_pos hirr 0
      omega
    have hB : m ≤ partialQuotient a 1 := Nat.find_min' hex hT
    have hprev : (m - 1) * partialQuotient a 0 + 1 < t :=
      Nat.lt_of_not_ge (Nat.find_min hex (by omega : m - 1 < m))
    obtain ⟨b, hbL, hbU, hbT⟩ := exists_second_block_bracket ha ha' hirr hpos hB
    refine ⟨m, hpos, hB, le_antisymm ?_ hnext⟩
    by_contra! hn
    exact b.not_record_between (by rw [hbL, hbU, max_lt_iff]; exact ⟨hprev, ht⟩)
      (hbT ▸ hn) hr
  · rintro ⟨m, hm, hm', rfl⟩
    obtain ⟨b, _, _, h⟩ := exists_second_block_bracket ha ha' hirr hm hm'
    rw [← h]
    exact b.record_at_sum hirr

/-- The block lengths in the source, including the exceptional previous
denominator q₋₁ = 1 for k = 0. -/
def ReversedFractions.fullPrefixLength (s : ReversedFractions) (k m : Nat) : Nat :=
  m * continuedDenominator s (k + 1) +
    (if k = 0 then 1 else continuedDenominator s k) - 2

def ReversedFractions.fullPrefixDigit (s : ReversedFractions) (k : Nat) : Nat :=
  if k = 0 then s.a 0 - 1 else s.a k

/-- The standard-word length recurrence with q₋₁ = q₀ = 1 and
d₁ = a₁ − 1, in the indexing of ct:palprefSturm. -/
theorem fullPrefixDenominator_step (s : ReversedFractions) (k : Nat) :
    continuedDenominator s (k + 2) =
      s.fullPrefixDigit k * continuedDenominator s (k + 1) +
        (if k = 0 then 1 else continuedDenominator s k) := by
  cases k with
  | zero =>
    have h := s.a_pos 0
    change s.a 0 * 1 + 0 = (s.a 0 - 1) * 1 + 1
    omega
  | succ k =>
    simp only [ReversedFractions.fullPrefixDigit, Nat.succ_ne_zero, if_false]
    rfl

/-- The complete list in ct:palprefSturm, including both initial blocks. -/
theorem characteristic_palPrefix_iff_full_continuant_blocks {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a) {L : Nat} (hL : 0 < L) :
    let s := slopeFractions a hirr
    PalPrefix (FactorTree.characteristicWord a) L ↔
      ∃ k m, 1 ≤ m ∧ m ≤ s.fullPrefixDigit k ∧ s.fullPrefixLength k m = L := by
  let s := slopeFractions a hirr
  let A := partialQuotient a 0
  let B := partialQuotient a 1
  have hA : 0 < A := partialQuotient_pos hirr 0
  have hbound : s.prefixBlocks.Q 1 - 1 = B * A := by
    change B * (A * 1 + 0) + 1 - 1 = B * A
    simp
  have hzero (m : Nat) : s.fullPrefixLength 0 m = m + 1 - 2 := by
    simp [ReversedFractions.fullPrefixLength, continuedDenominator]
  have hone (m : Nat) : s.fullPrefixLength 1 m = m * A + 1 - 2 := by
    change m * (A * 1 + 0) + 1 - 2 = _
    simp
  have htail (k m : Nat) : s.fullPrefixLength (k + 2) m = s.prefixBlocks.len k m := by
    unfold ReversedFractions.fullPrefixLength
    rw [if_neg (by omega : k + 2 ≠ 0)]
    rfl
  change PalPrefix (FactorTree.characteristicWord a) L ↔
    ∃ k m, 1 ≤ m ∧ m ≤ s.fullPrefixDigit k ∧ s.fullPrefixLength k m = L
  have hrec : PalPrefix (FactorTree.characteristicWord a) L ↔ FractionalRecord a (L + 2) :=
    characteristic_palPrefix_iff_fractional_record ha ha' hirr L
  constructor
  · intro h
    by_cases ht : s.prefixBlocks.Q 1 - 1 ≤ L
    · obtain ⟨k, m, hm, hm', he⟩ :=
        (characteristic_palPrefix_iff_continuant_block ha ha' hirr L ht).1 h
      exact ⟨k + 2, m, hm, hm', (htail k m).trans he⟩
    · rw [hbound] at ht
      by_cases hfirst : L + 2 ≤ A
      · refine ⟨0, L + 1, by omega, ?_, ?_⟩
        · change L + 1 ≤ A - 1
          omega
        · rw [hzero]
          omega
      · obtain ⟨m, hm, hm', he⟩ :=
          (second_block_record_iff ha ha' hirr (by omega : A < L + 2)
            (by omega : L + 2 ≤ B * A + 1)).1 (hrec.1 h)
        change m * A + 1 = L + 2 at he
        exact ⟨1, m, hm, hm', (hone m).trans (by omega)⟩
  · rintro ⟨k, m, hm, hm', he⟩
    rcases k with _ | _ | k
    · change m ≤ A - 1 at hm'
      rw [hzero] at he
      exact hrec.2 (early_fractionalRecord ha ha' hirr (by omega : L + 2 ≤ A))
    · change m ≤ B at hm'
      rw [hone] at he
      obtain ⟨b, _, _, hb⟩ := exists_second_block_bracket ha ha' hirr hm hm'
      change b.nextTime = m * A + 1 at hb
      apply hrec.2
      rw [show L + 2 = b.nextTime by omega]
      exact b.record_at_sum hirr
    · rw [htail] at he
      have hq := s.prefixBlocks.increasing.monotone (show 1 ≤ k + 1 by omega)
      have hprod := Nat.mul_le_mul_right (s.prefixBlocks.Q (k + 1)) hm
      simp only [one_mul] at hprod
      have hp := s.prefixBlocks.positive k
      change m * s.prefixBlocks.Q (k + 1) + s.prefixBlocks.Q k - 2 = L at he
      have ht : s.prefixBlocks.Q 1 - 1 ≤ L := by omega
      exact (characteristic_palPrefix_iff_continuant_block ha ha' hirr L ht).2
        ⟨k, m, hm, hm', he⟩

/-- The word-level form of Fischler's formula for the characteristic
mechanical word of an irrational slope. -/
theorem characteristic_below_density_iff {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) {p q : Nat} (hq : 0 < q) :
    BelowPalDensity (FactorTree.characteristicWord a) p q ↔
      (p : ℝ) / q < (slopeFractions a hirr).fischlerDensity :=
  below_density_iff_of_palindrome_blocks (slopeFractions a hirr) rfl _
    (characteristic_palPrefix_iff_continuant_block ha ha' hirr) hq

theorem characteristic_density_gt_half_iff_badlyApproximable {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a) :
    BelowPalDensity (FactorTree.characteristicWord a) 1 2 ↔ BadlyApproximable a := by
  rw [characteristic_below_density_iff ha ha' hirr (by decide)]
  simpa only [Nat.cast_one, Nat.cast_ofNat] using slope_density_gt_half_iff hirr

end Thesis.SturmianDensity
