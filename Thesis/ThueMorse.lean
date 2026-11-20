import Std.Tactic

namespace Thesis.ThueMorse

def digitSum (b n : Nat) : Nat :=
  if hb : 1 < b then
    if hn : 0 < n then
      have : n / b < n := Nat.div_lt_self hn hb
      digitSum b (n / b) + n % b
    else 0
  else 0
termination_by n

def word (b N n : Nat) : Nat := digitSum b n % N

@[simp] theorem digitSum_zero (b : Nat) : digitSum b 0 = 0 := by
  rw [digitSum]
  simp

theorem digitSum_block {b : Nat} (hb : 1 < b) (q r : Nat) (hr : r < b) :
    digitSum b (b * q + r) = digitSum b q + r := by
  by_cases hz : b * q + r = 0
  · have hq : q = 0 := by
      have hm : b * q = 0 := by omega
      rcases Nat.mul_eq_zero.mp hm with h | h
      · omega
      · exact h
    have he : r = 0 := by omega
    simp [hz, hq, he]
  · rw [digitSum, dif_pos hb, dif_pos (Nat.pos_of_ne_zero hz),
      Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    dsimp only
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]

/-- The digit-sum word is fixed by the substitution `t ↦ t (t+1) … (t+b-1)`. -/
theorem word_block {b N : Nat} (hb : 1 < b) (q r : Nat) (hr : r < b) :
    word b N (b * q + r) = (word b N q + r) % N := by
  simp only [word, digitSum_block hb q r hr, Nat.mod_add_mod]

/-- The fixed point starting at zero is unique, proving `tw:gTM`. -/
theorem fixed_point {b N : Nat} (hb : 1 < b) (w : Nat → Nat) (h0 : w 0 = 0)
    (hw : ∀ q r, r < b → w (b * q + r) = (w q + r) % N) :
    w = word b N := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · simp [hn, h0, word]
    · have hb0 : 0 < b := by omega
      have hr := Nat.mod_lt n hb0
      have hq := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hb
      have he : b * (n / b) + n % b = n := by
        rw [Nat.add_comm, Nat.mod_add_div]
      calc
        w n = (w (n / b) + n % b) % N := by
          simpa only [he] using hw (n / b) (n % b) hr
        _ = word b N n := by
          rw [ih _ hq, ← word_block hb _ _ hr, he]

/-- Each pair of successive blocks differs by adding the twist `j`
to every letter modulo `N`. Here `j` is a natural representative. -/
def StrongRepeat (b N k j : Nat) : Prop :=
  ∃ i m : Nat, 0 < m ∧ ∀ t < (k - 1) * m,
    word b N (i + t + m) = (word b N (i + t) + j) % N

/-- The periodic case of `tw:main`. -/
theorem periodic_case {b N : Nat} (hb : 1 < b) (hN : 0 < N)
    (h : N ∣ b - 1) :
    (∀ n, word b N n = n % N) ∧ ∀ k j, StrongRepeat b N k j := by
  obtain ⟨a, ha⟩ := h
  have he : b = 1 + N * a := by omega
  have hm (q : Nat) : (b * q) % N = q % N := by
    rw [he, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  have hs (n : Nat) : word b N n = n % N := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hn : n = 0
      · simp [hn, word]
      · have hr := Nat.mod_lt n (by omega : 0 < b)
        have hq := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hb
        have hdiv : b * (n / b) + n % b = n := by
          rw [Nat.add_comm, Nat.mod_add_div]
        calc
          word b N n = (word b N (n / b) + n % b) % N := by
            simpa only [hdiv] using word_block (N := N) hb (n / b) (n % b) hr
          _ = n % N := by
            rw [ih _ hq, ← hm (n / b), Nat.mod_add_mod, hdiv]
  refine ⟨hs, fun k j => ⟨0, j + N, by omega, ?_⟩⟩
  intro t _
  simp [hs, ← Nat.add_assoc, Nat.add_mod_right]

private theorem add_mod_cancel_right {a b r N : Nat} (hr : r ≤ N)
    (h : (a + r) % N = (b + r) % N) : a % N = b % N := by
  have he : r + (N - r) = N := by omega
  have hc := congrArg (fun x : Nat => (x + (N - r)) % N) h
  simpa only [Nat.mod_add_mod, Nat.add_assoc, he, Nat.add_mod_right] using hc

private theorem digitSum_even (q : Nat) : digitSum 2 (2 * q) = digitSum 2 q := by
  simpa using digitSum_block (by decide : 1 < 2) q 0 (by decide)

private theorem digitSum_odd (q : Nat) : digitSum 2 (2 * q + 1) = digitSum 2 q + 1 :=
  digitSum_block (by decide) q 1 (by decide)

private theorem binary_window {N j : Nat} (hN : 2 ≤ N) (m : Nat) (hm : 0 < m)
    (i : Nat) (h : ∀ t < 2 * m, word 2 N (i + t + m) = (word 2 N (i + t) + j) % N) :
    j % N = 1 := by
  by_cases he : m % 2 = 0
  · have hm' : m = 2 * (m / 2) := by omega
    apply binary_window hN (m / 2) (by omega) (i / 2)
    intro t ht
    have hr : i % 2 < 2 := by omega
    have hstep := h (2 * t) (by omega)
    have h1 : i + 2 * t + m = 2 * (i / 2 + t + m / 2) + i % 2 := by omega
    have h2 : i + 2 * t = 2 * (i / 2 + t) + i % 2 := by omega
    rw [h1, h2, word_block (by decide) _ _ hr, word_block (by decide) _ _ hr,
      Nat.mod_add_mod] at hstep
    rw [show word 2 N (i / 2 + t) + i % 2 + j =
        word 2 N (i / 2 + t) + j + i % 2 by omega] at hstep
    have hc := add_mod_cancel_right (by omega : i % 2 ≤ N) hstep
    simpa only [word, Nat.mod_mod] using hc
  · by_cases ho : m = 1
    · have ht : (i % 2) < 2 * m := by omega
      have hn : i + i % 2 = 2 * ((i + i % 2) / 2) := by omega
      have hstep := h (i % 2) ht
      rw [ho, hn, word_block (by decide) _ 1 (by decide),
        ← Nat.add_zero (2 * ((i + i % 2) / 2)),
        word_block (by decide) _ 0 (by decide)] at hstep
      simp only [Nat.add_zero, word, Nat.mod_mod, Nat.mod_add_mod] at hstep
      have hc := add_mod_cancel_right (Nat.le_of_lt (Nat.mod_lt _ (by omega)) : digitSum 2 ((i + i % 2) / 2) % N ≤ N)
        (a := j) (b := 1) (by
          rw [Nat.add_comm j, Nat.add_comm 1, Nat.mod_add_mod, Nat.mod_add_mod]
          exact hstep.symm)
      simpa [Nat.mod_eq_of_lt (show 1 < N by omega)] using hc
    · have ht : (5 - i % 4) % 4 + 1 < 2 * m := by omega
      let t := (5 - i % 4) % 4
      let q := (i + t) / 4
      let p := (i + t + m) / 2
      have h1 : i + t = 2 * (2 * q) + 1 := by dsimp [q, t]; omega
      have h2 : i + (t + 1) = 2 * (2 * q + 1) := by omega
      have h3 : i + t + m = 2 * p := by dsimp [p]; omega
      have h4 : i + (t + 1) + m = 2 * p + 1 := by omega
      have e1 := h t (by omega : t < 2 * m)
      have e2 := h (t + 1) ht
      have hsame : word 2 N (i + (t + 1)) = word 2 N (i + t) := by
        rw [h1, h2]
        simp only [word, digitSum_even, digitSum_odd]
      rw [hsame, ← e1, h3, h4] at e2
      simp only [word, digitSum_even, digitSum_odd] at e2
      have hc := add_mod_cancel_right (Nat.le_of_lt (Nat.mod_lt _ (by omega)) : digitSum 2 p % N ≤ N)
        (a := 1) (b := 0) (by
          rw [Nat.add_comm 1, Nat.zero_add, Nat.mod_add_mod, Nat.mod_mod]
          exact e2)
      simp [Nat.mod_eq_of_lt (show 1 < N by omega)] at hc
termination_by m

theorem binary_twist_necessary {N j : Nat} (hN : 2 ≤ N) (h : StrongRepeat 2 N 3 j) :
    j % N = 1 := by
  obtain ⟨i, m, hm, hw⟩ := h
  exact binary_window hN m hm i hw

private theorem digitSum_all_ones (n : Nat) : digitSum 2 (2 ^ n - 1) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := Nat.two_pow_pos n
    have he : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      rw [Nat.pow_succ, Nat.mul_comm]; omega
    rw [he, digitSum_odd, ih]

private theorem digitSum_power (n : Nat) : digitSum 2 (2 ^ n) = 1 := by
  induction n with
  | zero => simpa using digitSum_odd 0
  | succ n ih => rw [Nat.pow_succ, Nat.mul_comm, digitSum_even, ih]

/-- The binary avoidance theorem, `avoidance` in the corrected thesis. -/
theorem binary_twist_iff {N j : Nat} (hN : 2 ≤ N) :
    StrongRepeat 2 N 3 j ↔ j % N = 1 := by
  refine ⟨binary_twist_necessary hN, ?_⟩
  intro hj
  let i := 2 * (2 ^ (N - 1) - 1)
  have hp := Nat.two_pow_pos (N - 1)
  have hi : i + 1 + 1 = 2 ^ N := by
    have he : N = (N - 1) + 1 := by omega
    calc
      i + 1 + 1 = 2 ^ (N - 1) * 2 := by dsimp [i]; omega
      _ = 2 ^ N := by rw [← Nat.pow_succ]; exact congrArg (fun n : Nat => 2 ^ n) he.symm
  refine ⟨i, 1, by decide, ?_⟩
  intro t ht
  have ht' : t = 0 ∨ t = 1 := by omega
  rcases ht' with rfl | rfl
  · simp only [Nat.add_zero]
    simp only [i, word, digitSum_odd, digitSum_even, Nat.mod_add_mod,
      ← Nat.add_mod_mod _ j N, hj]
  · rw [hi]
    simp only [word, digitSum_power, i, digitSum_odd, digitSum_all_ones]
    rw [show N - 1 + 1 = N by omega, Nat.mod_self, Nat.zero_add, hj]
    exact Nat.mod_eq_of_lt (by omega)

end Thesis.ThueMorse
