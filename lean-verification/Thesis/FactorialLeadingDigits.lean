import Thesis.FactorialWord

namespace Thesis.FactorialWord

private theorem digits_push {b n d : Nat} (hb : 1 < b) (hn : 0 < n) (hd : d < b) :
    digits b (b * n + d) = d :: digits b n := by
  have hpos : 0 < b * n + d := by
    have := Nat.mul_pos (show 0 < b by omega) hn
    omega
  rw [digits_step hb hpos, Nat.mul_add_mod, Nat.mod_eq_of_lt hd,
    Nat.mul_add_div (by omega), Nat.div_eq_of_lt hd, Nat.add_zero]

private theorem extend_digits {b : Nat} (hb : 1 < b) (tail : List Nat)
    (ht : ∀ d ∈ tail, d < b) (n : Nat) (hn : 0 < n) :
    ∃ v > 0, (digits b v).reverse = (digits b n).reverse ++ tail := by
  induction tail generalizing n with
  | nil => exact ⟨n, hn, by simp⟩
  | cons a tail ih =>
    have ha := ht a (by simp)
    have hpos : 0 < b * n + a := by
      have := Nat.mul_pos (show 0 < b by omega) hn
      omega
    obtain ⟨v, hv, he⟩ := ih (fun d hd => ht d (List.mem_cons_of_mem _ hd)) _ hpos
    refine ⟨v, hv, ?_⟩
    simpa [digits_push hb hn ha, List.append_assoc] using he

private theorem encode_leading_digits {b a : Nat} (hb : 1 < b) (ha : a ≠ 0)
    (tail : List Nat) (h : ∀ d ∈ a :: tail, d < b) :
    ∃ v > 0, (digits b v).reverse = a :: tail := by
  have hab := h a (by simp)
  have he : digits b a = [a] := by
    rw [digits_step hb (by omega), Nat.mod_eq_of_lt hab, Nat.div_eq_of_lt hab,
      digits, dif_pos hb]
    simp
  obtain ⟨v, hv, hv'⟩ := extend_digits hb tail
    (fun d hd => h d (List.mem_cons_of_mem _ hd)) a (by omega)
  exact ⟨v, hv, by simpa [he] using hv'⟩

private theorem digits_zero (b : Nat) : digits b 0 = [] := by
  rw [digits]
  split <;> simp

private theorem digits_drop_power {b : Nat} (hb : 1 < b) (p n : Nat) :
    (digits b n).drop p = digits b (n / b ^ p) := by
  induction p generalizing n with
  | zero => simp
  | succ p ih =>
    by_cases hn : n = 0
    · simp [hn, digits_zero]
    · rw [digits_step hb (Nat.pos_of_ne_zero hn), List.drop_succ_cons, ih,
        Nat.div_div_eq_div_mul, Nat.pow_succ']

private def digitsValue (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + b * digitsValue b ds

private theorem digitsValue_digits {b : Nat} (hb : 1 < b) (n : Nat) :
    digitsValue b (digits b n) = n := by
  by_cases hn : n = 0
  · simp [hn, digits_zero, digitsValue]
  · rw [digits_step hb (Nat.pos_of_ne_zero hn), digitsValue,
      digitsValue_digits hb (n / b), Nat.mod_add_div]
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) hb

/-- The base-`b` interval for a leading block from `lem:lead`, expressed
before taking logarithms. `u` is the integer represented by the leading
block, and `p` counts the digits that follow it. -/
theorem leading_prefix_iff_scaled_interval {b n u : Nat} (hb : 1 < b) :
    (digits b u).reverse <+: (digits b n).reverse ↔
      ∃ p, u * b ^ p ≤ n ∧ n < (u + 1) * b ^ p := by
  constructor
  · intro h
    have hs : digits b u <:+ digits b n := by simpa using h.reverse
    obtain ⟨ds, hds⟩ := hs
    have hdrop := digits_drop_power hb ds.length n
    rw [← hds, List.drop_left] at hdrop
    have hv := congrArg (digitsValue b) hdrop
    rw [digitsValue_digits hb, digitsValue_digits hb] at hv
    refine ⟨ds.length, ?_, ?_⟩
    · exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).1 (Nat.le_of_eq hv)
    · exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).1 (by omega)
  · rintro ⟨p, hlo, hhi⟩
    have hdiv : n / b ^ p = u := Nat.div_eq_of_lt_le hlo hhi
    have hs : (digits b n).drop p <:+ digits b n := List.drop_suffix _ _
    rw [digits_drop_power hb, hdiv] at hs
    exact hs.reverse

/-- The arithmetic reduction in `lem:lead`. The input is the interval-hitting
consequence of uniform distribution of the fractional parts of
`log_b(n!)`; the distribution argument is kept as an explicit premise. -/
theorem leading_prefixes_of_scaled_intervals {b : Nat} (hb : 1 < b)
    (hhit : ∀ u > 0, ∀ minimum, ∃ n ≥ minimum, ∃ p,
      u * b ^ p ≤ factorial (n + 1) ∧ factorial (n + 1) < (u + 1) * b ^ p) :
    LeadingPrefixes b := by
  intro a tail ha hd minimum
  obtain ⟨u, hu, hword⟩ := encode_leading_digits hb ha tail hd
  obtain ⟨n, hn, p, hlo, hhi⟩ := hhit u hu minimum
  refine ⟨n, hn, ?_⟩
  rw [← hword]
  exact (leading_prefix_iff_scaled_interval hb).2 ⟨p, hlo, hhi⟩

end Thesis.FactorialWord
