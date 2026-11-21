import Thesis.ThueMorseRecurrence

namespace Thesis.ThueMorse

/-- The kth iterate of a constant-length substitution, as an indexed word. -/
def iterateSubstitution {b : Nat} (hb : 0 < b) (σ : A → Fin b → A) :
    (k : Nat) → A → Fin (b ^ k) → A
  | 0, a, _ => a
  | k + 1, a, i =>
    σ (iterateSubstitution hb σ k a
      ⟨i / b, (Nat.div_lt_iff_lt_mul hb).2 (by simpa only [pow_succ] using i.isLt)⟩)
      ⟨i % b, Nat.mod_lt _ hb⟩

/-- A primitive substitution has an iterate sending every one-letter
word to a word containing all letters. -/
def PrimitiveSubstitution {b : Nat} (hb : 0 < b) (σ : A → Fin b → A) : Prop :=
  ∃ k, ∀ a c, ∃ i : Fin (b ^ k), iterateSubstitution hb σ k a i = c

/-- A fixed word for a constant-length substitution. -/
def SubstitutionFixedWord {b : Nat} (σ : A → Fin b → A) (w : Nat → A) : Prop :=
  ∀ m (r : Fin b), w (b * m + r) = σ (w m) r

/-- Each finite iterate at the initial letter is the corresponding
prefix of any fixed word beginning with that letter. -/
theorem iterateSubstitution_eq_prefix_of_fixedWord {b : Nat} (hb : 0 < b)
    {σ : A → Fin b → A} {w : Nat → A} (hw : SubstitutionFixedWord σ w)
    (k : Nat) (i : Fin (b ^ k)) : iterateSubstitution hb σ k (w 0) i = w i.val := by
  induction k with
  | zero =>
    have hi : i.val = 0 := by
      have ht : i.val < 1 := by simpa only [pow_zero] using i.isLt
      omega
    simp [iterateSubstitution, hi]
  | succ k ih =>
    have hq : i.val / b < b ^ k :=
      (Nat.div_lt_iff_lt_mul hb).2 (by simpa only [pow_succ] using i.isLt)
    let r : Fin b := ⟨i.val % b, Nat.mod_lt _ hb⟩
    change σ (iterateSubstitution hb σ k (w 0) ⟨i.val / b, hq⟩) r = w i.val
    rw [ih, ← hw]
    congr 1
    change b * (i.val / b) + i.val % b = i.val
    rw [Nat.add_comm, Nat.mod_add_div]

/-- The substitution ξ_b(a) = a(a+1)…(a+b−1) modulo N. -/
def digitSubstitution (b N : Nat) (hN : 0 < N) (a : Fin N) (r : Fin b) : Fin N :=
  ⟨(a + r) % N, Nat.mod_lt _ hN⟩

theorem digitSubstitution_fixedWord {b N : Nat} (hb : 1 < b) (hN : 0 < N) :
    SubstitutionFixedWord (digitSubstitution b N hN) (finiteWord b N hN) := by
  intro m r
  apply Fin.ext
  exact word_block hb m r r.isLt

theorem iterate_digitSubstitution {b N : Nat} (hb : 1 < b) (hN : 0 < N)
    (k : Nat) (a : Fin N) (i : Fin (b ^ k)) :
    ((iterateSubstitution (Nat.zero_lt_one.trans hb) (digitSubstitution b N hN) k a i : Fin N) : Nat) =
      (a + digitSum b i) % N := by
  induction k with
  | zero =>
    have ht : i.val < 1 := by simpa only [pow_zero] using i.isLt
    have hi : i.val = 0 := by omega
    simp only [iterateSubstitution, hi, digitSum_zero, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]
  | succ k ih =>
    have hq : i.val / b < b ^ k := (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).2
      (by simpa only [pow_succ] using i.isLt)
    have hr : i.val % b < b := Nat.mod_lt _ (by omega)
    have he : b * (i.val / b) + i.val % b = i.val := by rw [Nat.add_comm, Nat.mod_add_div]
    change (((iterateSubstitution (Nat.zero_lt_one.trans hb) (digitSubstitution b N hN) k a
      ⟨i.val / b, hq⟩ : Fin N) : Nat) + i.val % b) % N = (a + digitSum b i) % N
    rw [ih, Nat.mod_add_mod, Nat.add_assoc]
    conv_rhs => rw [← he, digitSum_block hb _ _ hr]

/-- The precise iterate threshold in the primitivity claim. -/
theorem iterate_digitSubstitution_contains_letter {b N : Nat} (hb : 1 < b) (hN : 0 < N)
    (k : Nat) (hk : N - 1 ≤ k) (a c : Fin N) :
    ∃ i : Fin (b ^ k),
      iterateSubstitution (Nat.zero_lt_one.trans hb) (digitSubstitution b N hN) k a i = c := by
  obtain ⟨m, hm, ha⟩ := aligned_block_contains_letter hb hN (N - 1) 0 a le_rfl a.isLt
  simp only [Nat.mul_zero, Nat.zero_add] at ha
  obtain ⟨i, hi, hc⟩ := aligned_block_contains_letter hb hN k m c hk c.isLt
  refine ⟨⟨i, hi⟩, Fin.ext ?_⟩
  rw [iterate_digitSubstitution hb hN, ← ha]
  exact (word_aligned hb k m i hi).symm.trans hc

theorem digitSubstitution_primitive {b N : Nat} (hb : 1 < b) (hN : 0 < N) :
    PrimitiveSubstitution (Nat.zero_lt_one.trans hb) (digitSubstitution b N hN) :=
  ⟨N - 1, iterate_digitSubstitution_contains_letter hb hN (N - 1) le_rfl⟩

end Thesis.ThueMorse
