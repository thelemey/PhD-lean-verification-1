import Thesis.Palindrome

namespace Thesis

/-- Consecutive positive lengths of palindromic prefixes. -/
def ConsecutivePalPrefixes (w : Nat → α) (u v : Nat) : Prop :=
  0 < u ∧ u < v ∧ PalPrefix w u ∧ PalPrefix w v ∧
    ∀ n, u < n → n < v → ¬ PalPrefix w n

/-- The nonnegative rational strict lower cut of Fischler's density.
For infinitely many prefixes, the density is the liminf of the inverse
ratios `u/v`. A nonnegative rational `p/q` is below that liminf exactly
when all sufficiently late ratios are at least `p/q + 1/(q*t)` for some
positive integer `t`. A word with bounded prefix lengths has density zero,
whose nonnegative strict lower cut is empty. -/
def BelowPalDensity (w : Nat → α) (p q : Nat) : Prop :=
  0 < q ∧ (∀ k, ∃ n ≥ k, PalPrefix w n) ∧
    ∃ t > 0, ∃ K, ∀ u v, K ≤ u → ConsecutivePalPrefixes w u v →
      (p * t + 1) * v ≤ (q * t) * u

private theorem consecutive_insert (w : Nat → α) {u v : Nat}
    (hu : 0 < u) :
    ConsecutivePalPrefixes (insertSeparator w) (2 * u + 1) (2 * v + 1) ↔
      ConsecutivePalPrefixes w u v := by
  constructor
  · rintro ⟨_, huv, hp, hq, hgap⟩
    refine ⟨hu, by omega, (palPrefix_insert_odd w _).1 hp,
      (palPrefix_insert_odd w _).1 hq, ?_⟩
    intro n hnu hnv hn
    exact hgap (2 * n + 1) (by omega) (by omega) ((palPrefix_insert_odd w _).2 hn)
  · rintro ⟨_, huv, hp, hq, hgap⟩
    refine ⟨by omega, by omega, (palPrefix_insert_odd w _).2 hp,
      (palPrefix_insert_odd w _).2 hq, ?_⟩
    intro n hnu hnv hn
    obtain ⟨m, hm, hpref⟩ := (palPrefix_insert_iff w (by omega)).1 hn
    exact hgap m (by omega) (by omega) hpref

private theorem ratio_insert {a b u v : Nat} (huv : u < v)
    (h : a * v ≤ b * u) : a * (2 * v + 1) ≤ b * (2 * u + 1) := by
  have hab : a ≤ b := by
    by_cases he : a ≤ b
    · exact he
    · have he' : b < a := by omega
      have hlt := Nat.mul_lt_mul_of_pos_right he' (by omega : 0 < v)
      have hle := Nat.mul_le_mul_left b (Nat.le_of_lt huv)
      omega
  have ha : a * (2 * v) = 2 * (a * v) := by ac_rfl
  have hb : b * (2 * u) = 2 * (b * u) := by ac_rfl
  simp only [Nat.mul_add, Nat.mul_one, ha, hb]
  omega

private theorem ratio_remove {a b u v : Nat} (hv : b ≤ v)
    (h : (a + 1) * (2 * v + 1) ≤ b * (2 * u + 1)) :
    (a * 2 + 1) * v ≤ (b * 2) * u := by
  simp only [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.add_mul, Nat.one_mul] at h
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Proposition `prop:insertion` in the corrected thesis. Equality of the
nonnegative rational strict lower cuts determines equality of densities
in `[0,1]`, including density zero. -/
theorem palDensity_insert (w : Nat → α) (p q : Nat) :
    BelowPalDensity (insertSeparator w) p q ↔ BelowPalDensity w p q := by
  constructor
  · rintro ⟨hq, hunbounded, t, ht, K, htail⟩
    refine ⟨hq, (unbounded_palPrefixes_insert_iff w).1 hunbounded,
      t * 2, by omega, max K (q * t), ?_⟩
    intro u v hu h
    have huK : K ≤ u := Nat.le_trans (Nat.le_max_left _ _) hu
    have huv : u < v := h.2.1
    have hqv : q * t ≤ v := Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) hu) (Nat.le_of_lt huv)
    have hh := htail (2 * u + 1) (2 * v + 1) (by omega)
      ((consecutive_insert w h.1).2 h)
    rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    exact ratio_remove hqv hh
  · rintro ⟨hq, hunbounded, t, ht, K, htail⟩
    refine ⟨hq, (unbounded_palPrefixes_insert_iff w).2 hunbounded,
      t, ht, 2 * K + 3, ?_⟩
    intro U V hU h
    obtain ⟨u, hu, _⟩ := (palPrefix_insert_iff w h.1).1 h.2.2.1
    have hV : 0 < V := by have := h.2.1; omega
    obtain ⟨v, hv, _⟩ := (palPrefix_insert_iff w hV).1 h.2.2.2.1
    subst U
    subst V
    have hh := (consecutive_insert w (by omega : 0 < u)).1 h
    exact ratio_insert hh.2.1 (htail u v (by omega) hh)

end Thesis
