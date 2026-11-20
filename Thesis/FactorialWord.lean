import Std.Tactic

namespace Thesis.FactorialWord

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

private theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

private theorem factorial_dvd_factorial (m n : Nat) (h : m ≤ n) :
    factorial m ∣ factorial n := by
  induction n with
  | zero =>
    have he : m = 0 := by omega
    exact he ▸ Nat.dvd_refl _
  | succ n ih =>
    by_cases he : m = n + 1
    · exact he ▸ Nat.dvd_refl _
    · exact Nat.dvd_mul_left_of_dvd (ih (by omega)) (n + 1)

/-- A sufficient uniform threshold for `b ^ k ∣ n!`. -/
theorem pow_dvd_factorial {b : Nat} (hb : 0 < b) (k n : Nat) (hn : b * k ≤ n) :
    b ^ k ∣ factorial n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    let m := b * (k + 1) - 1
    have hp : 0 < b * (k + 1) := Nat.mul_pos hb (by omega)
    have eq : m + 1 = b * (k + 1) := by dsimp [m]; omega
    have hm : b * k ≤ m := by dsimp [m]; rw [Nat.mul_succ]; omega
    obtain ⟨p, hfac⟩ := ih m hm
    apply Nat.dvd_trans _ (factorial_dvd_factorial (m + 1) n (by omega))
    refine ⟨(k + 1) * p, ?_⟩
    rw [factorial, eq, hfac, Nat.pow_succ]
    ac_rfl

/-- The canonical base-`b` digits, least significant first. -/
def digits (b n : Nat) : List Nat :=
  if hb : 1 < b then
    if hn : 0 < n then
      have : n / b < n := Nat.div_lt_self hn hb
      n % b :: digits b (n / b)
    else []
  else []
termination_by n

private theorem digits_step {b n : Nat} (hb : 1 < b) (hn : 0 < n) :
    digits b n = n % b :: digits b (n / b) := by
  rw [digits, dif_pos hb, dif_pos hn]

private theorem zero_prefix {b : Nat} (hb : 1 < b) (k n : Nat)
    (hn : 0 < n) (h : b ^ k ∣ n) : List.replicate k 0 <+: digits b n := by
  induction k generalizing n with
  | zero => exact ⟨digits b n, rfl⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := h
    have hmul : n = b * (b ^ k * c) := by
      rw [hc, Nat.pow_succ]
      ac_rfl
    have hquot : n / b = b ^ k * c := by
      rw [hmul, Nat.mul_div_cancel_left _ (by omega)]
    have hqpos : 0 < n / b := by
      rw [hquot]
      apply Nat.pos_of_ne_zero
      intro he
      rw [he, Nat.mul_zero] at hmul
      omega
    obtain ⟨rest, hrest⟩ := ih (n / b) hqpos ⟨c, hquot⟩
    have hrem : n % b = 0 := by rw [hmul, Nat.mul_mod_right]
    refine ⟨rest, ?_⟩
    rw [digits_step hb hn, hrem, ← hrest, List.replicate_succ, List.cons_append]

/-- Lemma `lem:trail`. In least-significant-first order, trailing zeros
in the usual writing appear as a prefix. -/
theorem factorial_trailing_zeros {b : Nat} (hb : 1 < b) (k n : Nat) (hn : b * k ≤ n) :
    List.replicate k 0 <+: digits b (factorial n) :=
  zero_prefix hb k (factorial n) (factorial_pos n) (pow_dvd_factorial (by omega) k n hn)

private theorem split_leading_zeros (w : List Nat) :
    (∃ k, w = List.replicate k 0) ∨
      ∃ k a tail, a ≠ 0 ∧ w = List.replicate k 0 ++ a :: tail := by
  induction w with
  | nil => exact .inl ⟨0, rfl⟩
  | cons a tail ih =>
    by_cases ha : a = 0
    · subst a
      rcases ih with ⟨k, rfl⟩ | ⟨k, a, tail, h, rfl⟩
      · exact .inl ⟨k + 1, rfl⟩
      · exact .inr ⟨k + 1, a, tail, h, rfl⟩
    · exact .inr ⟨0, a, tail, ha, rfl⟩

/-- The concatenation step of `mainthm01`, conditional on `lem:lead`.
Every finite word occurs within at most two successive factorial blocks. -/
theorem occurs_given_arbitrarily_late_prefixes {b : Nat} (hb : 1 < b)
    (prefixes : ∀ (a : Nat) (tail : List Nat), a ≠ 0 →
      (∀ d ∈ a :: tail, d < b) →
      ∀ bound : Nat, ∃ n ≥ bound,
        a :: tail <+: (digits b (factorial (n + 1))).reverse)
    (w : List Nat) (hw : ∀ d ∈ w, d < b) :
    ∃ n, w <:+: (digits b (factorial n)).reverse ++
        (digits b (factorial (n + 1))).reverse := by
  rcases split_leading_zeros w with ⟨k, rfl⟩ | ⟨k, a, tail, ha, rfl⟩
  · obtain ⟨left, hleft⟩ := factorial_trailing_zeros hb k (b * k) (Nat.le_refl _)
    have he := congrArg List.reverse hleft
    simp only [List.reverse_append, List.reverse_replicate] at he
    exact ⟨b * k, left.reverse, _, congrArg (fun block => block ++ _) he⟩
  · have ht : ∀ d ∈ a :: tail, d < b := by
      intro d hd
      exact hw d (List.mem_append_right _ hd)
    obtain ⟨n, hn, right, hright⟩ := prefixes a tail ha ht (b * k)
    obtain ⟨left, hleft⟩ := factorial_trailing_zeros hb k n hn
    have he := congrArg List.reverse hleft
    simp only [List.reverse_append, List.reverse_replicate] at he
    exact ⟨n, left.reverse, right, by rw [← he, ← hright]; simp [List.append_assoc]⟩

end Thesis.FactorialWord
