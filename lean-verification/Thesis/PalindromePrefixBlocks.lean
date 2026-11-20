import Thesis.PalPrefixRatio

open Filter Topology

namespace Thesis.SturmianDensity

/-- A tail of the length blocks mq_k+q_{k-1}-2 appearing in the
palindromic-prefix enumeration for a characteristic Sturmian word. -/
structure PalindromePrefixBlocks where
  Q : Nat → Nat
  d : Nat → Nat
  positive : ∀ k, 0 < Q k
  increasing : StrictMono Q
  step : ∀ k, Q (k + 2) = d k * Q (k + 1) + Q k
  digit_pos : ∀ k, 0 < d k

namespace PalindromePrefixBlocks

def len (s : PalindromePrefixBlocks) (k m : Nat) : Nat :=
  m * s.Q (k + 1) + s.Q k - 2

def first (s : PalindromePrefixBlocks) (k : Nat) : Nat := s.len k 1

def last (s : PalindromePrefixBlocks) (k : Nat) : Nat := s.len k (s.d k)

theorem Q_next_ge_two (s : PalindromePrefixBlocks) (k : Nat) : 2 ≤ s.Q (k + 1) := by
  have ha := s.positive k
  have hb := s.increasing (Nat.lt_succ_self k)
  change s.Q k < s.Q (k + 1) at hb
  omega

theorem first_pos (s : PalindromePrefixBlocks) (k : Nat) : 0 < s.first k := by
  unfold first len
  simp only [one_mul]
  have ha := s.positive k
  have hb := Q_next_ge_two s k
  omega

theorem len_order (s : PalindromePrefixBlocks) (k : Nat) {i j : Nat}
    (hi : 1 ≤ i) (h : i < j) : s.len k i < s.len k j := by
  have hQ := s.positive (k + 1)
  have h₂ := Q_next_ge_two s k
  have hd := s.positive k
  have hprod := Nat.mul_lt_mul_of_pos_right h hQ
  have hlow := Nat.mul_le_mul_right (s.Q (k + 1)) hi
  dsimp only [len]
  simp only [one_mul] at hlow
  omega

theorem len_mono (s : PalindromePrefixBlocks) (k : Nat) {i j : Nat}
    (hi : 1 ≤ i) (h : i ≤ j) : s.len k i ≤ s.len k j := by
  rcases lt_or_eq_of_le h with h' | rfl
  · exact (s.len_order k hi h').le
  · exact le_rfl

theorem last_eq (s : PalindromePrefixBlocks) (k : Nat) : s.last k = s.Q (k + 2) - 2 := by
  unfold last len
  rw [s.step]

theorem last_strictMono (s : PalindromePrefixBlocks) : StrictMono s.last := by
  intro i j hij
  rw [s.last_eq i, s.last_eq j]
  have h := s.increasing (show i + 2 < j + 2 by omega)
  have h' : 2 ≤ s.Q (i + 2) := s.Q_next_ge_two (i + 1)
  omega

theorem first_next_eq (s : PalindromePrefixBlocks) (k : Nat) :
    s.first (k + 1) = s.last k + s.Q (k + 1) := by
  unfold first len
  rw [s.last_eq]
  have h : 2 ≤ s.Q (k + 2) := s.Q_next_ge_two (k + 1)
  simp only [one_mul]
  change s.Q (k + 2) + s.Q (k + 1) - 2 = s.Q (k + 2) - 2 + s.Q (k + 1)
  omega

theorem first_strictMono (s : PalindromePrefixBlocks) : StrictMono s.first := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h := s.len_mono k (i := 1) (j := s.d k) le_rfl (s.digit_pos k)
  change s.first k ≤ s.last k at h
  rw [s.first_next_eq]
  have hp := s.positive (k + 1)
  omega

theorem earlier_block_lt (s : PalindromePrefixBlocks) {i j m n : Nat}
    (hij : i < j) (hm : 1 ≤ m) (hm' : m ≤ s.d i) (hn : 1 ≤ n) :
    s.len i m < s.len j n := by
  have h₁ : s.len i m ≤ s.last i := s.len_mono i hm hm'
  have h₂ : s.last i < s.first (i + 1) := by rw [s.first_next_eq]; have := s.positive (i+1); omega
  have h₃ := s.first_strictMono.monotone (Nat.succ_le_of_lt hij)
  have h₄ : s.first j ≤ s.len j n := s.len_mono j le_rfl hn
  exact ((h₁.trans_lt h₂).trans_le h₃).trans_le h₄

private theorem len_succ (s : PalindromePrefixBlocks) (k m : Nat) (hm : 1 ≤ m) :
    s.len k (m + 1) = s.len k m + s.Q (k + 1) := by
  have hQ := s.Q_next_ge_two k
  have hlow := Nat.mul_le_mul_right (s.Q (k + 1)) hm
  simp only [len, Nat.add_mul, one_mul] at *
  omega

/-- The increment to the next palindrome length is q_k, both within the
kth block and when passing from its last length to the next block. -/
theorem next_len (s : PalindromePrefixBlocks) (k m : Nat) (hm : 1 ≤ m) (hm' : m ≤ s.d k) :
    (∃ i j, 1 ≤ j ∧ j ≤ s.d i ∧ s.len i j = s.len k m + s.Q (k + 1)) ∧
    (∀ i j, 1 ≤ j → j ≤ s.d i → s.len k m < s.len i j →
      s.len k m + s.Q (k + 1) ≤ s.len i j) := by
  constructor
  · rcases lt_or_eq_of_le hm' with h | rfl
    · exact ⟨k, m + 1, by omega, by omega, s.len_succ k m hm⟩
    · exact ⟨k + 1, 1, le_rfl, s.digit_pos _, s.first_next_eq k⟩
  · intro i j hj hj' hv
    rcases lt_trichotomy i k with h | rfl | h
    · exact False.elim ((not_lt_of_ge (s.earlier_block_lt h hj hj' hm).le) hv)
    · have hmj : m < j := by
        by_contra hne
        exact (not_lt_of_ge (s.len_mono i hj (by omega))) hv
      rw [← s.len_succ i m hm]
      exact s.len_mono i (by omega) (by omega)
    · have h₁ : s.len k m ≤ s.last k := s.len_mono k hm hm'
      have h₂ := s.first_strictMono.monotone (Nat.succ_le_of_lt h)
      have h₃ : s.first i ≤ s.len i j := s.len_mono i le_rfl hj
      rw [s.first_next_eq] at h₂
      exact ((Nat.add_le_add_right h₁ _).trans h₂).trans h₃

/-- The largest ratio inside the block, including the transition to
the next block, is attained at its first length. -/
noncomputable def rawPeak (s : PalindromePrefixBlocks) (k : Nat) : ℝ :=
  1 + (s.Q (k + 1) : ℝ) / (s.first k : ℝ)

private theorem actual_next_len (s : PalindromePrefixBlocks) {P : Nat → Nat}
    (hmono : StrictMono P) {K : Nat}
    (hBlocks : ∀ L ≥ K, (∃ i, P i = L) ↔ ∃ k m, 1 ≤ m ∧ m ≤ s.d k ∧ s.len k m = L)
    {i k m : Nat} (hK : K ≤ P i) (hm : 1 ≤ m) (hm' : m ≤ s.d k) (he : P i = s.len k m) :
    P (i + 1) = P i + s.Q (k + 1) := by
  obtain ⟨⟨l, j, hj, hj', hn⟩, hmin⟩ := s.next_len k m hm hm'
  have hK' : K ≤ P i + s.Q (k + 1) := by omega
  obtain ⟨z, hz⟩ := (hBlocks _ hK').2 ⟨l, j, hj, hj', hn.trans (by rw [he])⟩
  have hiz : i < z := hmono.lt_iff_lt.1 (by rw [hz]; have := s.positive (k + 1); omega)
  have hnext : P i < P (i + 1) := hmono (Nat.lt_succ_self _)
  obtain ⟨u, v, hv, hv', he'⟩ := (hBlocks _ (hK.trans hnext.le)).1 ⟨i + 1, rfl⟩
  have hle := hmin u v hv hv' (by rw [he']; exact he ▸ hnext)
  rw [he', ← he] at hle
  exact le_antisymm ((hmono.monotone (Nat.succ_le_of_lt hiz)).trans_eq hz) hle

private theorem ratio_le_peak (s : PalindromePrefixBlocks) {P : Nat → Nat}
    {i k m : Nat} (hm : 1 ≤ m) (he : P i = s.len k m)
    (hnext : P (i + 1) = P i + s.Q (k + 1)) :
    (P (i + 1) : ℝ) / P i ≤ s.rawPeak k := by
  have hden : s.first k ≤ P i := (s.len_mono k le_rfl hm).trans_eq he.symm
  have hpos : 0 < (s.first k : ℝ) := by exact_mod_cast s.first_pos k
  have hP : 0 < (P i : ℝ) := by exact_mod_cast (s.first_pos k).trans_le hden
  rw [hnext, Nat.cast_add, add_div, div_self hP.ne', rawPeak]
  exact add_le_add_left (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos (by exact_mod_cast hden)) _

private theorem ratio_eq_peak (s : PalindromePrefixBlocks) {P : Nat → Nat}
    {i k : Nat} (he : P i = s.first k) (hnext : P (i + 1) = P i + s.Q (k + 1)) :
    (P (i + 1) : ℝ) / P i = s.rawPeak k := by
  have hP : (P i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (he.symm ▸ (s.first_pos k).ne')
  rw [hnext, Nat.cast_add, add_div, div_self hP, he, rawPeak]

/-- Taking the limsup of all consecutive ratios is equivalent to taking
the limsup of the first ratio in each length block. A finite initial
segment of the enumeration does not affect this identity. -/
theorem limsup_ratios_eq_rawPeak (s : PalindromePrefixBlocks) {P : Nat → Nat}
    (hmono : StrictMono P) {K : Nat}
    (hBlocks : ∀ L ≥ K, (∃ i, P i = L) ↔ ∃ k m, 1 ≤ m ∧ m ≤ s.d k ∧ s.len k m = L) :
    limsup (fun i => (P (i + 1) : ℝ) / P i) atTop = limsup s.rawPeak atTop := by
  simp only [limsup_eq]
  congr 1
  ext a
  change (∀ᶠ i in atTop, (P (i + 1) : ℝ) / P i ≤ a) ↔
    (∀ᶠ k in atTop, s.rawPeak k ≤ a)
  constructor
  · intro h
    obtain ⟨I, hI⟩ := eventually_atTop.1 h
    filter_upwards [s.first_strictMono.tendsto_atTop.eventually
      (eventually_ge_atTop (max K (P I)))] with k hk
    have hK : K ≤ s.first k := (le_max_left _ _).trans hk
    obtain ⟨i, hi⟩ := (hBlocks _ hK).2 ⟨k, 1, le_rfl, s.digit_pos k, rfl⟩
    have hIi : I ≤ i := hmono.le_iff_le.1 ((le_max_right _ _).trans (hk.trans_eq hi.symm))
    have hr := s.actual_next_len hmono hBlocks (hK.trans_eq hi.symm) le_rfl (s.digit_pos k) hi
    rw [← s.ratio_eq_peak hi hr]
    exact hI i hIi
  · intro h
    obtain ⟨J, hJ⟩ := eventually_atTop.1 h
    filter_upwards [hmono.tendsto_atTop.eventually
      (eventually_ge_atTop (max K (s.last J + 1)))] with i hi
    have hK : K ≤ P i := (le_max_left _ _).trans hi
    obtain ⟨k, m, hm, hm', he⟩ := (hBlocks _ hK).1 ⟨i, rfl⟩
    have hge : J ≤ k := by
      by_contra hne
      have hh := s.last_strictMono.monotone (show k ≤ J by omega)
      have h₁ : s.len k m ≤ s.last k := s.len_mono k hm hm'
      have h₂ := (le_max_right K (s.last J + 1)).trans hi
      omega
    exact (s.ratio_le_peak hm he.symm (s.actual_next_len hmono hBlocks hK hm hm' he.symm)).trans
      (hJ k hge)

end PalindromePrefixBlocks
end Thesis.SturmianDensity
