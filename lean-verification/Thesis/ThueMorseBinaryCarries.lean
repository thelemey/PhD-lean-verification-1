import Thesis.ThueMorseCarries

namespace Thesis.ThueMorse

/-- The even indices of a window of length (4m) give a window of
length (2m) after division by two, as in `lem:half`. -/
theorem binary_digitDelta_reduce_window {N i m : Nat} {j : ℤ}
    (h : ∀ n, i ≤ n → n < i + 2 * (2 * m) → digitDelta 2 (2 * m) n ≡ j [ZMOD (N : ℤ)]) :
    ∀ n, (i + 1) / 2 ≤ n → n < (i + 1) / 2 + 2 * m → digitDelta 2 m n ≡ j [ZMOD (N : ℤ)] := by
  intro n hlo hhi
  have he := h (2 * n) (by omega) (by omega)
  rw [← Nat.add_zero (2 * n), digitDelta_scale (by decide : 1 < 2) m n 0 (by decide)] at he
  exact he

/-- The two identities from `lem:half`. -/
theorem binary_digitDelta_even (m n : Nat) :
    digitDelta 2 (2 * m) (2 * n) = digitDelta 2 m n := by
  simpa using digitDelta_scale (by decide : 1 < 2) m n 0 (by decide)

theorem binary_digitDelta_succ_sub (m n : Nat) :
    digitDelta 2 m (n + 1) - digitDelta 2 m n =
      (multiplicity 2 (n + 1) : ℤ) - multiplicity 2 (n + m + 1) := by
  rw [digitDelta_succ_sub (by decide : 1 < 2)]
  push_cast
  ring

private theorem binary_delta_one (n : Nat) :
    digitDelta 2 1 n = 1 - (multiplicity 2 (n + 1) : ℤ) := by
  unfold digitDelta
  rw [digitSum_succ_of_trailingExponent (by decide : 1 < 2)]
  push_cast
  ring

private theorem four_dvd_shift_of_constant_delta {N i m n : Nat} {j : ℤ}
    (hN : 2 ≤ N) (hm : m % 2 = 1)
    (h : ∀ x, i ≤ x → x < i + 2 * m → digitDelta 2 m x ≡ j [ZMOD (N : ℤ)])
    (hlo : i ≤ n) (hhi : n + 1 < i + 2 * m) (hn : n % 2 = 0) :
    4 ∣ n + m + 1 := by
  have hodd : ¬ 2 ∣ n + 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have heven : 2 ∣ n + m + 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hd := (h (n + 1) (by omega) hhi).sub (h n hlo (by omega))
  rw [binary_digitDelta_succ_sub, multiplicity_eq_zero.2 hodd, Nat.cast_zero, zero_sub, sub_self] at hd
  have hmod : multiplicity 2 (n + m + 1) ≡ 0 [MOD N] := by
    apply Int.natCast_modEq_iff.1
    simpa only [neg_neg, neg_zero, Nat.cast_zero] using hd.neg
  have hdiv : N ∣ multiplicity 2 (n + m + 1) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simpa [Nat.ModEq] using hmod
  have hp : 0 < multiplicity 2 (n + m + 1) := Nat.pos_of_ne_zero
    (fun he => (multiplicity_eq_zero.1 he) heven)
  have hfinite : FiniteMultiplicity 2 (n + m + 1) := Nat.finiteMultiplicity_iff.2 ⟨by decide, by omega⟩
  exact hfinite.pow_dvd_iff_le_multiplicity.2 (hN.trans (Nat.le_of_dvd hp hdiv))

/-- An odd block length in `lem:odd` must be one. Two odd
indices two apart would otherwise force two multiples of four two apart. -/
theorem binary_odd_window {N i m : Nat} {j : ℤ} (hN : 2 ≤ N) (hm : m % 2 = 1)
    (h : ∀ n, i ≤ n → n < i + 2 * m → digitDelta 2 m n ≡ j [ZMOD (N : ℤ)]) :
    m = 1 ∧ j ≡ 1 [ZMOD (N : ℤ)] := by
  let n := i + i % 2
  have he : n % 2 = 0 := by dsimp [n]; omega
  have hlo : i ≤ n := by dsimp [n]; omega
  have hle : n ≤ i + 1 := by dsimp [n]; omega
  by_cases hm1 : m = 1
  · subst m
    have hodd : ¬ 2 ∣ n + 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    have hd := h n hlo (by omega)
    rw [binary_delta_one, multiplicity_eq_zero.2 hodd, Nat.cast_zero, sub_zero] at hd
    exact ⟨rfl, hd.symm⟩
  · have h₁ := four_dvd_shift_of_constant_delta hN hm h hlo (by omega) he
    have h₂ := four_dvd_shift_of_constant_delta hN hm h (n := n + 2) (by omega) (by omega) (by omega)
    rw [Nat.dvd_iff_mod_eq_zero] at h₁ h₂
    omega

/-- Repeatedly halving an even block reduces a constant window to the odd case. -/
theorem binary_window_twist {N : Nat} {j : ℤ} (hN : 2 ≤ N) (m i : Nat) (hm : 0 < m)
    (h : ∀ n, i ≤ n → n < i + 2 * m → digitDelta 2 m n ≡ j [ZMOD (N : ℤ)]) :
    j ≡ 1 [ZMOD (N : ℤ)] := by
  induction m using Nat.strongRecOn generalizing i with
  | ind m ih =>
    by_cases he : m % 2 = 0
    · have hm' : m = 2 * (m / 2) := by omega
      have h' : ∀ n, i ≤ n → n < i + 2 * (2 * (m / 2)) →
          digitDelta 2 (2 * (m / 2)) n ≡ j [ZMOD (N : ℤ)] := by simpa only [← hm'] using h
      exact ih (m / 2) (by omega) ((i + 1) / 2) (by omega) (binary_digitDelta_reduce_window h')
    · exact (binary_odd_window hN (by omega) h).2

/-- The two comparisons starting at (2^N-2) both have twist one. -/
theorem binary_delta_witness {N : Nat} (hN : 2 ≤ N) :
    ∀ n, 2 ^ N - 2 ≤ n → n < 2 ^ N - 2 + 2 → digitDelta 2 1 n ≡ 1 [ZMOD (N : ℤ)] := by
  let i := 2 ^ N - 2
  have hNpos : 0 < N := by omega
  have hpow : 1 ≤ 2 ^ (N - 1) := Nat.two_pow_pos (N - 1)
  have he : 2 ^ N = 2 ^ (N - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hNpos]
  have hi : i + 2 = 2 ^ N := by dsimp [i]; omega
  have hodd : ¬ 2 ∣ i + 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  intro n hlo hhi
  change i ≤ n at hlo
  change n < i + 2 at hhi
  have hn : n = i ∨ n = i + 1 := by omega
  rcases hn with rfl | rfl
  · rw [binary_delta_one, multiplicity_eq_zero.2 hodd, Nat.cast_zero, sub_zero]
  · rw [binary_delta_one, show i + 1 + 1 = 2 ^ N by omega,
      multiplicity_pow_self (by decide : (2 : Nat) ≠ 0) (by simp : ¬ IsUnit (2 : Nat))]
    have hzero : (N : ℤ) ≡ 0 [ZMOD (N : ℤ)] := by simp [Int.ModEq]
    simpa only [sub_zero] using (Int.ModEq.refl (1 : ℤ)).sub hzero

end Thesis.ThueMorse
