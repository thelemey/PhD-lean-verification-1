import Std.Tactic

namespace Thesis

/-- A prefix of length `n` agrees with its reversal. -/
def PalPrefix (w : Nat → α) (n : Nat) : Prop :=
  ∀ i < n, w i = w (n - 1 - i)

/-- The new letter is represented by `none`, so it lies outside the old alphabet. -/
def insertSeparator (w : Nat → α) (i : Nat) : Option α :=
  if i % 2 = 0 then none else some (w (i / 2))

/-- The odd-length part of the palindrome-prefix correspondence. -/
theorem palPrefix_insert_odd (w : Nat → α) (m : Nat) :
    PalPrefix (insertSeparator w) (2 * m + 1) ↔ PalPrefix w m := by
  constructor
  · intro h i hi
    have he := h (2 * i + 1) (by omega)
    have hr : 2 * m + 1 - 1 - (2 * i + 1) = 2 * (m - 1 - i) + 1 := by omega
    rw [hr] at he
    have letter (j : Nat) : insertSeparator w (2 * j + 1) = some (w j) := by
      unfold insertSeparator
      have hp : (2 * j + 1) % 2 ≠ 0 := by omega
      have hd : (2 * j + 1) / 2 = j := by omega
      rw [if_neg hp, hd]
    simpa only [letter, Option.some.injEq] using he
  · intro h i hi
    unfold insertSeparator
    by_cases hp : i % 2 = 0
    · have hr : (2 * m + 1 - 1 - i) % 2 = 0 := by omega
      rw [if_pos hp, if_pos hr]
    · have hr : (2 * m + 1 - 1 - i) % 2 ≠ 0 := by omega
      have hd : (2 * m + 1 - 1 - i) / 2 = m - 1 - i / 2 := by omega
      rw [if_neg hp, if_neg hr, hd, h (i / 2) (by omega)]

theorem not_palPrefix_insert_even (w : Nat → α) {m : Nat} (hm : 0 < m) :
    ¬ PalPrefix (insertSeparator w) (2 * m) := by
  intro h
  have he := h 0 (by omega)
  have hr : (2 * m - 1) % 2 ≠ 0 := by omega
  simp [insertSeparator, hr] at he

/-- Lemma `lem:interleave` in the corrected thesis. -/
theorem palPrefix_insert_iff (w : Nat → α) {n : Nat} (hn : 0 < n) :
    PalPrefix (insertSeparator w) n ↔ ∃ m, n = 2 * m + 1 ∧ PalPrefix w m := by
  constructor
  · intro h
    by_cases hp : n % 2 = 0
    · have he : n = 2 * (n / 2) := by omega
      rw [he] at h
      exact False.elim (not_palPrefix_insert_even w (by omega) h)
    · have he : n = 2 * (n / 2) + 1 := by omega
      exact ⟨n / 2, he, (palPrefix_insert_odd w (n / 2)).mp (he ▸ h)⟩
  · rintro ⟨m, rfl, hm⟩
    exact (palPrefix_insert_odd w m).mpr hm

/-- Insertion preserves the existence of arbitrarily long palindromic
prefixes, covering the finite-prefix case of the density convention. -/
theorem unbounded_palPrefixes_insert_iff (w : Nat → α) :
    (∀ k, ∃ n ≥ k, PalPrefix (insertSeparator w) n) ↔
      ∀ k, ∃ n ≥ k, PalPrefix w n := by
  constructor
  · intro h k
    obtain ⟨n, hn, hp⟩ := h (2 * k + 1)
    obtain ⟨m, he, hm⟩ := (palPrefix_insert_iff w (by omega)).mp hp
    exact ⟨m, by omega, hm⟩
  · intro h k
    obtain ⟨n, hn, hp⟩ := h k
    exact ⟨2 * n + 1, by omega, (palPrefix_insert_odd w n).mpr hp⟩

end Thesis
