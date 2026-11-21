import Thesis.ThueMorseClassification
import Thesis.ThueMorseCarries
import Thesis.ThueMorseSubstitution
import Mathlib.GroupTheory.Perm.Cycle.Basic

namespace Thesis.ThueMorse

variable {A : Type*}

/-- The strong block condition from def:strong_repetition. Position r
in block q is obtained from position r in the initial block by δ^q. -/
def StrongBlockRepeat (w : Nat → A) (δ : Equiv.Perm A) (k : Nat) : Prop :=
  ∃ i m : Nat, 0 < m ∧ ∀ q < k, ∀ r < m, w (i + q * m + r) = (δ ^ q) (w (i + r))

/-- The adjacent-block criterion in tw:lem(a), for any permutation. -/
theorem strongBlockRepeat_iff_adjacent (w : Nat → A) (δ : Equiv.Perm A) (k : Nat) :
    StrongBlockRepeat w δ k ↔
      ∃ i m : Nat, 0 < m ∧ ∀ t < (k - 1) * m, w (i + t + m) = δ (w (i + t)) := by
  constructor
  · rintro ⟨i, m, hm, hb⟩
    refine ⟨i, m, hm, fun t ht => ?_⟩
    let q := t / m
    let r := t % m
    have hq : q < k - 1 := (Nat.div_lt_iff_lt_mul hm).2 ht
    have hr : r < m := Nat.mod_lt _ hm
    have hsplit : t = q * m + r := by
      dsimp only [q, r]
      exact (Nat.mod_add_div t m).symm.trans (by ac_rfl)
    have hprev : i + t = i + q * m + r := by omega
    have hnext : i + t + m = i + (q + 1) * m + r := by rw [Nat.succ_mul]; omega
    have hq0 : q < k := hq.trans_le (Nat.sub_le _ _)
    have hk : 1 ≤ k := Nat.one_le_of_lt hq0
    have hq1 : q + 1 < k := by
      simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] using Nat.succ_lt_succ hq
    rw [hnext, hprev, hb q hq0 r hr, hb (q + 1) hq1 r hr,
      pow_succ', Equiv.Perm.mul_apply]
  · rintro ⟨i, m, hm, hw⟩
    refine ⟨i, m, hm, fun q hq r hr => ?_⟩
    induction q with
    | zero => simp
    | succ q ih =>
      have hprod : (q + 1) * m ≤ (k - 1) * m := Nat.mul_le_mul_right m (by omega)
      rw [Nat.succ_mul] at hprod
      have ht : q * m + r < (k - 1) * m := by omega
      have h := hw (q * m + r) ht
      have he : i + (q + 1) * m + r = i + (q * m + r) + m := by rw [Nat.succ_mul]; omega
      have hprev : i + (q * m + r) = i + q * m + r := by omega
      rw [he, h, hprev, ih (by omega), pow_succ', Equiv.Perm.mul_apply]

/-- The fixed-point letters before identifying the alphabet with residues. -/
def wordOnCycle (σ : Equiv.Perm A) (a₀ : A) (b : Nat) (n : Nat) : A :=
  (σ ^ digitSum b n) a₀

theorem wordOnCycle_zero (σ : Equiv.Perm A) (a₀ : A) (b : Nat) :
    wordOnCycle σ a₀ b 0 = a₀ := by simp [wordOnCycle]

theorem wordOnCycle_block (σ : Equiv.Perm A) (a₀ : A) {b : Nat} (hb : 1 < b)
    (q r : Nat) (hr : r < b) :
    wordOnCycle σ a₀ b (b * q + r) = (σ ^ r) (wordOnCycle σ a₀ b q) := by
  rw [wordOnCycle, digitSum_block hb q r hr, add_comm, pow_add, Equiv.Perm.mul_apply, wordOnCycle]

/-- The substitution fixed point beginning with a₀, expressed using σ
on the original alphabet, as in prop:gTM and tw:gTM. -/
theorem wordOnCycle_unique_fixedPoint (σ : Equiv.Perm A) (a₀ : A) {b : Nat}
    (hb : 1 < b) (w : Nat → A) (h₀ : w 0 = a₀)
    (hw : ∀ q r, r < b → w (b * q + r) = (σ ^ r) (w q)) : w = wordOnCycle σ a₀ b := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · simp [hn, h₀, wordOnCycle_zero]
    have hr := Nat.mod_lt n (zero_lt_one.trans hb)
    have hq := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hb
    have he : b * (n / b) + n % b = n := by rw [Nat.add_comm, Nat.mod_add_div]
    calc
      w n = (σ ^ (n % b)) (w (n / b)) := by simpa only [he] using hw (n / b) (n % b) hr
      _ = wordOnCycle σ a₀ b n := by rw [ih _ hq, ← wordOnCycle_block σ a₀ hb _ _ hr, he]

/-- ξ_b on the original cycle, in its order from the source. -/
def cycleSubstitution (σ : Equiv.Perm A) (b : Nat) (a : A) (r : Fin b) : A :=
  (σ ^ r.val) a

theorem wordOnCycle_isFixedWord (σ : Equiv.Perm A) (a₀ : A) {b : Nat} (hb : 1 < b) :
    SubstitutionFixedWord (cycleSubstitution σ b) (wordOnCycle σ a₀ b) :=
  fun q r => wordOnCycle_block σ a₀ hb q r r.isLt

/-- The finite iterates of a₀ are prefixes of the fixed word of ξ_b. -/
theorem iterate_cycleSubstitution (σ : Equiv.Perm A) (a₀ : A) {b : Nat} (hb : 1 < b)
    (k : Nat) (i : Fin (b ^ k)) :
    iterateSubstitution (zero_lt_one.trans hb) (cycleSubstitution σ b) k a₀ i =
      wordOnCycle σ a₀ b i.val := by
  simpa only [wordOnCycle_zero] using
    iterateSubstitution_eq_prefix_of_fixedWord (zero_lt_one.trans hb)
      (wordOnCycle_isFixedWord σ a₀ hb) k i

section Cyclic

variable [Fintype A] {σ : Equiv.Perm A}
variable (hσ : σ.IsCycleOn (Finset.univ : Finset A))
variable (a₀ : A)

private theorem card_pos_of_letter (a : A) : 0 < Fintype.card A :=
  Fintype.card_pos_iff.2 ⟨a⟩

/-- The representative in [0,N), also for negative twists. -/
def twistResidue (N : Nat) (j : ℤ) : Nat := (j % (N : ℤ)).toNat

theorem twistResidue_cast {N : Nat} (hN : 0 < N) (j : ℤ) :
    (twistResidue N j : ℤ) = j % (N : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))

theorem twistResidue_lt {N : Nat} (hN : 0 < N) (j : ℤ) : twistResidue N j < N := by
  exact_mod_cast (show (twistResidue N j : ℤ) < N by
    rw [twistResidue_cast hN]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast hN))

/-- The positive representative j' from tw:main, including j = 0 modulo N. -/
theorem positiveTwist_residue_spec {N : Nat} (hN : 0 < N) (j : ℤ) :
    let j' := positiveTwist N (twistResidue N j)
    0 < j' ∧ j' ≤ N ∧ (j' : ℤ) ≡ j [ZMOD (N : ℤ)] := by
  intro j'
  have hres := twistResidue_lt hN j
  have hmod := Nat.mod_eq_of_lt hres
  have hj : 0 < j' ∧ j' ≤ N ∧ j' % N = twistResidue N j := by
    dsimp only [j', positiveTwist]
    rw [hmod]
    split
    · rename_i hzero
      simp [hzero, hN]
    · rename_i hne
      exact ⟨Nat.pos_of_ne_zero hne, hres.le, hmod⟩
  have hnat : j' ≡ twistResidue N j [MOD N] := hj.2.2.trans hmod.symm
  have hInt := Int.natCast_modEq_iff.2 hnat
  refine ⟨hj.1, hj.2.1, hInt.trans ?_⟩
  change (twistResidue N j : ℤ) % (N : ℤ) = j % (N : ℤ)
  rw [twistResidue_cast hN, Int.emod_emod]

theorem positiveTwist_residue_unique {N k : Nat} (hN : 0 < N) (j : ℤ)
    (hk₁ : 0 < k) (hk₂ : k ≤ N) (hk : (k : ℤ) ≡ j [ZMOD (N : ℤ)]) :
    k = positiveTwist N (twistResidue N j) := by
  let r := positiveTwist N (twistResidue N j)
  have ⟨hr₁, hr₂, hr⟩ := positiveTwist_residue_spec hN j
  change 0 < r at hr₁
  change r ≤ N at hr₂
  change (r : ℤ) ≡ j [ZMOD (N : ℤ)] at hr
  have h := Int.natCast_modEq_iff.1 (hk.trans hr.symm)
  change k % N = r % N at h
  change k = r
  rcases eq_or_lt_of_le hk₂ with rfl | hkl
  · rcases eq_or_lt_of_le hr₂ with he | hrl
    · exact he.symm
    · rw [Nat.mod_self, Nat.mod_eq_of_lt hrl] at h
      omega
  · rcases eq_or_lt_of_le hr₂ with he | hrl
    · rw [Nat.mod_eq_of_lt hkl, he, Nat.mod_self] at h
      omega
    · simpa only [Nat.mod_eq_of_lt hkl, Nat.mod_eq_of_lt hrl] using h

include hσ

/-- The residue numbering σ^t(a₀) used in the thesis. -/
noncomputable def cycleAlphabetEquiv : Fin (Fintype.card A) ≃ A :=
  Equiv.ofBijective (fun t => (σ ^ t.val) a₀) ⟨by
    intro r s h
    have hmod := (hσ.pow_apply_eq_pow_apply (Finset.mem_univ a₀)).1 h
    change r.val % (Finset.univ : Finset A).card =
      s.val % (Finset.univ : Finset A).card at hmod
    apply Fin.ext
    simpa only [Finset.card_univ, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt s.isLt] using hmod, by
    intro a
    obtain ⟨i, hi, he⟩ := hσ.exists_pow_eq (Finset.mem_univ a₀) (Finset.mem_univ a)
    exact ⟨⟨i, by simpa only [Finset.card_univ] using hi⟩, he⟩⟩

theorem cycleAlphabetEquiv_finiteWord (b n : Nat) :
    cycleAlphabetEquiv hσ a₀ (finiteWord b (Fintype.card A) (card_pos_of_letter a₀) n) =
      wordOnCycle σ a₀ b n := by
  change (σ ^ (digitSum b n % Fintype.card A)) a₀ = (σ ^ digitSum b n) a₀
  rw [hσ.pow_apply_eq_pow_apply (Finset.mem_univ a₀), Finset.card_univ]
  exact Nat.mod_mod _ _

/-- The primitivity assertion in thm:dynWb(1) on the original alphabet. -/
theorem iterate_cycleSubstitution_contains_letter {b : Nat} (hb : 1 < b)
    (k : Nat) (hk : Fintype.card A - 1 ≤ k) (a c : A) :
    ∃ i : Fin (b ^ k), iterateSubstitution (zero_lt_one.trans hb) (cycleSubstitution σ b) k a i = c := by
  obtain ⟨j, hj, hjc⟩ := hσ.exists_pow_eq (Finset.mem_univ a) (Finset.mem_univ c)
  have hj' : j < Fintype.card A := by simpa only [Finset.card_univ] using hj
  let start : Fin (Fintype.card A) := ⟨0, card_pos_of_letter a⟩
  let target : Fin (Fintype.card A) := ⟨j, hj'⟩
  obtain ⟨i, hi⟩ :=
    iterate_digitSubstitution_contains_letter hb (card_pos_of_letter a) k hk start target
  have hsum : digitSum b i.val % Fintype.card A = j := by
    have hi' := congrArg Fin.val hi
    rw [iterate_digitSubstitution hb (card_pos_of_letter a)] at hi'
    simpa only [start, target, Nat.zero_add] using hi'
  refine ⟨i, ?_⟩
  rw [iterate_cycleSubstitution σ a hb, ← hjc, wordOnCycle,
    hσ.pow_apply_eq_pow_apply (Finset.mem_univ a), Finset.card_univ]
  exact hsum.trans (Nat.mod_eq_of_lt hj').symm

private theorem zpow_apply_residue (j : ℤ) (a : A) :
    (σ ^ j) a = (σ ^ twistResidue (Fintype.card A) j) a := by
  rw [← zpow_natCast, hσ.zpow_apply_eq_zpow_apply (Finset.mem_univ a), Finset.card_univ]
  change j % (Fintype.card A : ℤ) =
    (twistResidue (Fintype.card A) j : ℤ) % (Fintype.card A : ℤ)
  rw [twistResidue_cast (card_pos_of_letter a), Int.emod_emod]

/-- Relabeling σ^t(a₀) by t modulo the cycle length preserves exactly
the adjacent-block condition, hence also the block condition. -/
theorem strongBlockRepeat_wordOnCycle_iff (b k : Nat) (j : ℤ) :
    StrongBlockRepeat (wordOnCycle σ a₀ b) (σ ^ j) k ↔
      StrongRepeat b (Fintype.card A) k (twistResidue (Fintype.card A) j) := by
  rw [strongBlockRepeat_iff_adjacent]
  unfold StrongRepeat
  have hpoint (i t m : Nat) :
      wordOnCycle σ a₀ b (i + t + m) = (σ ^ j) (wordOnCycle σ a₀ b (i + t)) ↔
        word b (Fintype.card A) (i + t + m) =
          (word b (Fintype.card A) (i + t) + twistResidue (Fintype.card A) j) % Fintype.card A := by
    rw [zpow_apply_residue hσ]
    unfold wordOnCycle
    rw [← Equiv.Perm.mul_apply, ← pow_add,
      hσ.pow_apply_eq_pow_apply (Finset.mem_univ a₀), Finset.card_univ]
    change _ % _ = _ % _ ↔ _
    rw [word, word, Nat.add_comm (digitSum b (i + t) % Fintype.card A), Nat.add_mod_mod]
  exact ⟨fun ⟨i, m, hm, h⟩ => ⟨i, m, hm, fun t ht => (hpoint i t m).1 (h t ht)⟩,
    fun ⟨i, m, hm, h⟩ => ⟨i, m, hm, fun t ht => (hpoint i t m).2 (h t ht)⟩⟩

/-- The modulus condition for one comparison inside a repeated block. -/
theorem wordOnCycle_step_iff_digitDelta (b i m : Nat) (j : ℤ) :
    wordOnCycle σ a₀ b (i + m) = (σ ^ j) (wordOnCycle σ a₀ b i) ↔
      digitDelta b m i ≡ j [ZMOD (Fintype.card A : ℤ)] := by
  unfold wordOnCycle digitDelta
  rw [← zpow_natCast, ← zpow_natCast, ← Equiv.Perm.mul_apply, ← zpow_add,
    hσ.zpow_apply_eq_zpow_apply (Finset.mem_univ a₀), Finset.card_univ, add_comm j]
  constructor
  · intro h
    simpa using Int.ModEq.sub_right (digitSum b i : ℤ) h
  · intro h
    simpa only [sub_add_cancel, add_comm j] using Int.ModEq.add_right (digitSum b i : ℤ) h

/-- The window criterion of `tw:lem(a)` on the original alphabet. -/
theorem strongBlockRepeat_iff_digitDelta (b k : Nat) (j : ℤ) :
    StrongBlockRepeat (wordOnCycle σ a₀ b) (σ ^ j) k ↔
      ∃ i m : Nat, 0 < m ∧ ∀ n, i ≤ n → n < i + (k - 1) * m →
        digitDelta b m n ≡ j [ZMOD (Fintype.card A : ℤ)] := by
  rw [strongBlockRepeat_iff_adjacent]
  constructor
  · rintro ⟨i, m, hm, hw⟩
    refine ⟨i, m, hm, fun n hlo hhi => ?_⟩
    have he : i + (n - i) = n := by omega
    have h := hw (n - i) (by omega)
    rw [he] at h
    exact (wordOnCycle_step_iff_digitDelta hσ a₀ b n m j).1 h
  · rintro ⟨i, m, hm, hw⟩
    exact ⟨i, m, hm, fun t ht => (wordOnCycle_step_iff_digitDelta hσ a₀ b (i + t) m j).2
      (hw (i + t) (by omega) (by omega))⟩

/-- The original alphabet and integer twists in the periodic case of tw:main. -/
theorem wordOnCycle_periodic_case {b : Nat} (hb : 1 < b) (h : Fintype.card A ∣ b - 1) :
    (∀ n, wordOnCycle σ a₀ b n = (σ ^ n) a₀) ∧
      ∀ k (j : ℤ), StrongBlockRepeat (wordOnCycle σ a₀ b) (σ ^ j) k := by
  obtain ⟨hword, hrep⟩ := periodic_case hb (card_pos_of_letter a₀) h
  constructor
  · intro n
    rw [wordOnCycle, hσ.pow_apply_eq_pow_apply (Finset.mem_univ a₀), Finset.card_univ]
    exact hword n
  · intro k j
    exact (strongBlockRepeat_wordOnCycle_iff hσ a₀ b k j).2 (hrep _ _)

/-- The nonperiodic threshold of tw:main for the original permutation. -/
theorem wordOnCycle_twisted_critical_exponent {b k : Nat} (hb : 1 < b) (hk : 2 ≤ k)
    (haper : ¬ Fintype.card A ∣ b - 1) (j : ℤ) :
    StrongBlockRepeat (wordOnCycle σ a₀ b) (σ ^ j) k ↔
      k ≤ max 2 (2 * b / positiveTwist (Fintype.card A) (twistResidue (Fintype.card A) j)) :=
  (strongBlockRepeat_wordOnCycle_iff hσ a₀ b k j).trans
    (twisted_critical_exponent hb (card_pos_of_letter a₀) hk haper)

/-- The binary avoidance theorem, including the negative integer twists in its statement. -/
theorem wordOnCycle_binary_avoidance (hN : 2 ≤ Fintype.card A) (j : ℤ) :
    ¬ StrongBlockRepeat (wordOnCycle σ a₀ 2) (σ ^ j) 3 ↔
      ¬ j ≡ 1 [ZMOD (Fintype.card A : ℤ)] := by
  have hpos : 0 < Fintype.card A := by omega
  have hj := twistResidue_lt hpos j
  have h1 : (1 : ℤ) % (Fintype.card A : ℤ) = 1 :=
    Int.emod_eq_of_lt (by decide) (by exact_mod_cast hN)
  rw [strongBlockRepeat_wordOnCycle_iff hσ a₀, binary_twist_iff hN, Nat.mod_eq_of_lt hj]
  change (¬ twistResidue (Fintype.card A) j = 1) ↔ ¬ j % (Fintype.card A : ℤ) = 1 % _
  rw [h1, ← twistResidue_cast hpos]
  exact not_congr (by exact_mod_cast (Iff.rfl :
    twistResidue (Fintype.card A) j = 1 ↔ twistResidue (Fintype.card A) j = 1))

/-- The full binary threshold in tw:cor, for every admissible k. -/
theorem wordOnCycle_binary_threshold (hN : 2 ≤ Fintype.card A) {k : Nat}
    (hk : 2 ≤ k) (j : ℤ) :
    StrongBlockRepeat (wordOnCycle σ a₀ 2) (σ ^ j) k ↔
      k ≤ if j ≡ 1 [ZMOD (Fintype.card A : ℤ)] then 4 else 2 := by
  have hp : 0 < Fintype.card A := by omega
  have hnonperiodic : ¬ Fintype.card A ∣ 2 - 1 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2 - 1) h
    omega
  rw [wordOnCycle_twisted_critical_exponent hσ a₀ (by decide) hk hnonperiodic]
  let r := positiveTwist (Fintype.card A) (twistResidue (Fintype.card A) j)
  change (k ≤ max 2 (4 / r)) ↔ _
  by_cases hj : j ≡ 1 [ZMOD (Fintype.card A : ℤ)]
  · have hr : r = 1 :=
      (positiveTwist_residue_unique (k := 1) hp j (by decide) (by omega) hj.symm).symm
    simp [hr, hj]
  · have ⟨hpos, _, hres⟩ := positiveTwist_residue_spec hp j
    change 0 < r at hpos
    change (r : ℤ) ≡ j [ZMOD (Fintype.card A : ℤ)] at hres
    have hne : r ≠ 1 := by
      intro he
      rw [he] at hres
      exact hj hres.symm
    have hr : 4 / r ≤ 2 := by
      apply (Nat.div_le_iff_le_mul hpos).2
      omega
    simp [hj, max_eq_left hr]

end Cyclic

end Thesis.ThueMorse
