import Std.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Multiplicity

namespace Thesis.FactorialWord

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem factorial_eq_nat (n : Nat) : factorial n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [factorial, Nat.factorial_succ, ih]

/-- The valuation estimate in lem:trail, by the first term of Legendre's sum. -/
theorem prime_factorization_factorial_ge_div {p n : Nat} (hp : p.Prime) :
    n / p ≤ (factorial n).factorization p := by
  let bound := Nat.log p n + 2
  have hbound : Nat.log p n < bound := by dsimp [bound]; omega
  have hmem : 1 ∈ Finset.Ico 1 bound := by
    rw [Finset.mem_Ico]
    exact ⟨le_rfl, by dsimp [bound]; omega⟩
  have h := (hp.pow_dvd_factorial_iff hbound).2
    (show n / p ≤ ∑ i ∈ Finset.Ico 1 bound, n / p ^ i by
      simpa only [pow_one] using
        (Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) hmem))
  rw [factorial_eq_nat]
  exact (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero n)).1 h

private theorem factorization_pos_of_mem {b p : Nat} (hp : p ∈ b.primeFactors) :
    0 < b.factorization p := by
  rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hp
  exact Nat.pos_of_ne_zero hp

/-- A sufficient uniform threshold, using the bounds on each prime
valuation of the base as in lem:trail. -/
theorem pow_dvd_factorial {b : Nat} (hb : 0 < b) (k n : Nat) (hn : b * k ≤ n) :
    b ^ k ∣ factorial n := by
  apply (Nat.factorization_le_iff_dvd (pow_ne_zero _ hb.ne') (factorial_pos n).ne').1
  rw [Nat.factorization_pow]
  intro p
  change k * b.factorization p ≤ (factorial n).factorization p
  by_cases hp : p ∈ b.primeFactors
  · have hprime := Nat.prime_of_mem_primeFactors hp
    have he : p ^ b.factorization p ≤ b :=
      Nat.le_of_dvd hb ((hprime.pow_dvd_iff_le_factorization hb.ne').2 le_rfl)
    have he' : p * b.factorization p ≤ b := by
      have hf := factorization_pos_of_mem hp
      have hd : b.factorization p ≤ p ^ (b.factorization p - 1) := by
        have hlt : b.factorization p - 1 < 2 ^ (b.factorization p - 1) := Nat.lt_two_pow_self
        exact (by omega : b.factorization p ≤ 2 ^ (b.factorization p - 1)).trans
          (Nat.pow_le_pow_left hprime.two_le _)
      calc
        _ ≤ p * (p ^ (b.factorization p - 1)) := Nat.mul_le_mul_left _ hd
        _ = p ^ b.factorization p := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ b.factorization p)]
        _ ≤ b := he
    have hmul : k * b.factorization p * p ≤ n := by
      calc
        _ = (p * b.factorization p) * k := by ac_rfl
        _ ≤ b * k := Nat.mul_le_mul_right _ he'
        _ ≤ n := hn
    exact ((Nat.le_div_iff_mul_le hprime.pos).2 hmul).trans
      (prime_factorization_factorial_ge_div hprime)
  · rw [← Nat.support_factorization, Finsupp.not_mem_support_iff] at hp
    simp [hp]

/-- The canonical base-`b` digits, least significant first. -/
def digits (b n : Nat) : List Nat :=
  if hb : 1 < b then
    if hn : 0 < n then
      have : n / b < n := Nat.div_lt_self hn hb
      n % b :: digits b (n / b)
    else []
  else []
termination_by n

theorem digits_step {b n : Nat} (hb : 1 < b) (hn : 0 < n) :
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

private theorem dvd_of_zero_prefix {b : Nat} (hb : 1 < b) (k n : Nat) (hn : 0 < n)
    (h : List.replicate k 0 <+: digits b n) : b ^ k ∣ n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, digits_step hb hn, List.cons_prefix_cons] at h
    have hquot : 0 < n / b := by
      have he := Nat.mod_add_div n b
      rw [← h.1, zero_add] at he
      by_cases hzero : n / b = 0
      · rw [hzero, Nat.mul_zero] at he
        exact (hn.ne' he.symm).elim
      · exact Nat.pos_of_ne_zero hzero
    obtain ⟨c, hc⟩ := ih (n / b) hquot h.2
    refine ⟨c, ?_⟩
    calc
      n = b * (n / b) := by simpa only [← h.1, zero_add] using (Nat.mod_add_div n b).symm
      _ = b ^ (k + 1) * c := by rw [hc, pow_succ']; ac_rfl

/-- The number of trailing zeros in the canonical writing of a positive integer. -/
def trailingZeroCount (b n : Nat) : Nat := ((digits b n).takeWhile (· == 0)).length

private theorem le_length_takeWhile_zero {xs : List Nat} {k : Nat} :
    k ≤ (xs.takeWhile (· == 0)).length ↔ List.replicate k 0 <+: xs := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      by_cases hx : x = 0
      · subst x
        simpa [List.replicate_succ, Nat.succ_le_succ_iff] using (ih (xs := xs))
      · simp [List.replicate_succ, hx, Ne.symm hx]

theorem le_trailingZeroCount_iff_dvd {b n : Nat} (hb : 1 < b) (hn : 0 < n) (k : Nat) :
    k ≤ trailingZeroCount b n ↔ b ^ k ∣ n :=
  le_length_takeWhile_zero.trans ⟨dvd_of_zero_prefix hb k n hn, zero_prefix hb k n hn⟩

/-- The prime valuation minimum in the source's proof of lem:trail. -/
theorem factorial_trailingZeroCount_eq_min {b : Nat} (hb : 1 < b) (n : Nat) :
    let values := b.primeFactors.image fun p => (factorial n).factorization p / b.factorization p
    trailingZeroCount b (factorial n) = values.min'
      ((Nat.nonempty_primeFactors.2 hb).image _) := by
  intro values
  have he (k : Nat) : k ≤ trailingZeroCount b (factorial n) ↔
      ∀ p ∈ b.primeFactors, k ≤ (factorial n).factorization p / b.factorization p := by
    rw [le_trailingZeroCount_iff_dvd hb (factorial_pos n), ← Nat.factorization_le_iff_dvd
      (pow_ne_zero _ (by omega : b ≠ 0)) (factorial_pos n).ne', Nat.factorization_pow]
    constructor
    · intro h p hp
      exact (Nat.le_div_iff_mul_le (factorization_pos_of_mem hp)).2 (h p)
    · intro h p
      change k * b.factorization p ≤ (factorial n).factorization p
      by_cases hp : p ∈ b.primeFactors
      · exact (Nat.le_div_iff_mul_le (factorization_pos_of_mem hp)).1 (h p hp)
      · rw [← Nat.support_factorization, Finsupp.not_mem_support_iff] at hp
        simp [hp]
  have hmin (k : Nat) : k ≤ trailingZeroCount b (factorial n) ↔
      k ≤ values.min' ((Nat.nonempty_primeFactors.2 hb).image _) := by
    rw [he, Finset.le_min'_iff]
    simp only [values, Finset.mem_image]
    constructor
    · intro h x hx
      obtain ⟨p, hp, heq⟩ := hx
      rw [← heq]
      exact h p hp
    · intro h p hp
      exact h _ ⟨p, hp, rfl⟩
  exact le_antisymm ((hmin _).1 le_rfl) ((hmin _).2 le_rfl)

theorem factorial_trailingZeroCount_monotone {b : Nat} (hb : 1 < b) :
    Monotone fun n => trailingZeroCount b (factorial n) := by
  intro m n h
  let k := trailingZeroCount b (factorial m)
  apply (le_trailingZeroCount_iff_dvd hb (factorial_pos n) k).2
  apply dvd_trans ((le_trailingZeroCount_iff_dvd hb (factorial_pos m) k).1 le_rfl)
  simpa only [factorial_eq_nat] using Nat.factorial_dvd_factorial h

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

theorem digit_of_concatenation {b : Nat} (hb : 1 < b) (n d : Nat)
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
