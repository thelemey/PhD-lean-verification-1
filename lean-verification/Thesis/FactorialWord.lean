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

/-- The first `n` factorial blocks in the usual digit order, starting at `0!`. -/
def concatenation (b : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => concatenation b n ++ (digits b (factorial n)).reverse

theorem concatenation_prefix (b n : Nat) :
    concatenation b n <+: concatenation b (n + 1) :=
  List.prefix_append _ _

theorem concatenation_length_ge {b : Nat} (hb : 1 < b) (n : Nat) :
    n ≤ (concatenation b n).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [concatenation, List.length_append, List.length_reverse,
      digits_step hb (factorial_pos n), List.length_cons]
    omega

/-- Finite factors of the infinite concatenation are the factors of these
nested finite prefixes. -/
def Factor (b : Nat) (w : List Nat) : Prop :=
  ∃ n, w <:+: concatenation b n

/-- A finite arithmetic factor uses positions with a positive common
difference, all lying in some finite prefix of the concatenation. -/
def ArithmeticFactor (b : Nat) (w : List Nat) : Prop :=
  ∃ n start step : Nat, 0 < step ∧
    ∀ i (hi : i < w.length), (concatenation b n)[start + step * i]? = some w[i]

def LeadingPrefixes (b : Nat) : Prop :=
  ∀ (a : Nat) (tail : List Nat), a ≠ 0 →
    (∀ d ∈ a :: tail, d < b) →
    ∀ bound : Nat, ∃ n ≥ bound, a :: tail <+: (digits b (factorial (n + 1))).reverse

private theorem digit_lt {b : Nat} (hb : 1 < b) (n d : Nat)
    (hd : d ∈ digits b n) : d < b := by
  by_cases hn : 0 < n
  · rw [digits_step hb hn, List.mem_cons] at hd
    rcases hd with rfl | ht
    · exact Nat.mod_lt _ (by omega)
    · exact digit_lt hb (n / b) d ht
  · rw [digits, dif_pos hb, dif_neg hn] at hd
    exact False.elim (List.not_mem_nil hd)
termination_by n
decreasing_by exact Nat.div_lt_self hn hb

private theorem digit_of_concatenation {b : Nat} (hb : 1 < b) (n d : Nat)
    (hd : d ∈ concatenation b n) : d < b := by
  induction n with
  | zero => exact False.elim (List.not_mem_nil hd)
  | succ n ih =>
    rw [concatenation, List.mem_append, List.mem_reverse] at hd
    exact hd.elim ih (digit_lt hb _ _)

theorem factor_iff_digits {b : Nat} (hb : 1 < b) (hp : LeadingPrefixes b) (w : List Nat) :
    Factor b w ↔ ∀ d ∈ w, d < b := by
  constructor
  · rintro ⟨n, hn⟩ d hd
    exact digit_of_concatenation hb n d (hn.mem hd)
  · intro hw
    obtain ⟨n, hn⟩ := occurs_given_arbitrarily_late_prefixes hb hp w hw
    refine ⟨n + 2, hn.trans ?_⟩
    refine ⟨concatenation b n, [], ?_⟩
    simp [concatenation, List.append_assoc]

theorem factor_is_arithmetic {b : Nat} {w : List Nat} (h : Factor b w) :
    ArithmeticFactor b w := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨start, _, hs⟩ := List.isInfix_iff.mp hn
  refine ⟨n, start, 1, by decide, ?_⟩
  intro i hi
  simpa [Nat.add_comm] using hs i hi

theorem arithmeticFactor_iff_digits {b : Nat} (hb : 1 < b) (hp : LeadingPrefixes b)
    (w : List Nat) : ArithmeticFactor b w ↔ ∀ d ∈ w, d < b := by
  constructor
  · rintro ⟨n, start, step, _, hs⟩ d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
    exact digit_of_concatenation hb n _ (List.mem_of_getElem? (hs i hi))
  · intro hw
    exact factor_is_arithmetic ((factor_iff_digits hb hp w).2 hw)

/-- All `k`-letter words over the digits `0, …, b - 1`. -/
def allWords (b : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range b).flatMap fun d => (allWords b k).map (d :: ·)

theorem mem_allWords (b k : Nat) (w : List Nat) :
    w ∈ allWords b k ↔ w.length = k ∧ ∀ d ∈ w, d < b := by
  induction k generalizing w with
  | zero => cases w <;> simp [allWords]
  | succ k ih =>
    cases w with
    | nil => simp [allWords]
    | cons a w =>
      simp only [allWords, List.mem_flatMap, List.mem_range, List.mem_map, List.cons.injEq,
        List.length_cons, Nat.add_right_cancel_iff, List.mem_cons]
      constructor
      · rintro ⟨d, hd, v, hv, rfl, rfl⟩
        obtain ⟨hl, hh⟩ := (ih _).1 hv
        exact ⟨hl, fun d hd' => hd'.elim (fun he => he.symm ▸ hd) (hh d)⟩
      · rintro ⟨hl, hw⟩
        exact ⟨a, hw a (.inl rfl), w, (ih w).2 ⟨hl, fun d hd => hw d (.inr hd)⟩, rfl, rfl⟩

theorem nodup_allWords (b k : Nat) : (allWords b k).Nodup := by
  induction k with
  | zero => simp [allWords]
  | succ k ih =>
    rw [allWords, List.Nodup, List.pairwise_flatMap]
    constructor
    · intro a _
      rw [List.pairwise_map]
      exact ih.imp (fun hne he => hne (List.cons.inj he).2)
    · apply List.Pairwise.imp _ List.nodup_range
      intro a d hne u hu v hv he
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      exact hne (List.cons.inj he).1

private theorem length_prefixed_blocks (ds : List Nat) (words : List (List Nat)) :
    (ds.flatMap fun d => words.map (d :: ·)).length = ds.length * words.length := by
  induction ds with
  | nil => simp
  | cons a ds ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem length_allWords (b k : Nat) : (allWords b k).length = b ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [allWords, length_prefixed_blocks, List.length_range, ih, Nat.pow_succ, Nat.mul_comm]

/-- Both full complexities in `mainthm01`, conditional on the leading-digit lemma.
The same duplicate-free enumeration represents both languages at length `k`. -/
theorem full_complexities_of_leading_prefixes {b : Nat} (hb : 1 < b)
    (hp : LeadingPrefixes b) (k : Nat) :
    ∃ words : List (List Nat), words.Nodup ∧ words.length = b ^ k ∧
      (∀ w, w ∈ words ↔ w.length = k ∧ Factor b w) ∧
      (∀ w, w ∈ words ↔ w.length = k ∧ ArithmeticFactor b w) := by
  refine ⟨allWords b k, nodup_allWords b k, length_allWords b k, ?_, ?_⟩
  · intro w
    rw [factor_iff_digits hb hp, mem_allWords]
  · intro w
    rw [arithmeticFactor_iff_digits hb hp, mem_allWords]

end Thesis.FactorialWord
