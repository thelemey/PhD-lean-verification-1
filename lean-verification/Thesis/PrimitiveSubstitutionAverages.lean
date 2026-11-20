import Thesis.ConstantLengthBlocks
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

open Filter Set
open scoped Topology BigOperators

namespace Thesis.ThueMorse

variable {A : Type*} {b : Nat}

/-- Mean value of a function on the letters of an iterated substitution block. -/
noncomputable def substitutionAverage (hb : 0 < b) (σ : A → Fin b → A)
    (k : Nat) (f : A → ℝ) (a : A) : ℝ :=
  (∑ j : Fin (b ^ k), f (iterateSubstitution hb σ k a j)) / (b ^ k : Nat)

theorem substitutionAverage_nonempty_bounds (hb : 0 < b) (σ : A → Fin b → A)
    (k : Nat) (f : A → ℝ) (a : A) {lo hi : ℝ} (hf : ∀ c, f c ∈ Icc lo hi) :
    substitutionAverage hb σ k f a ∈ Icc lo hi := by
  have hB : 0 < ((b ^ k : Nat) : ℝ) := by exact_mod_cast Nat.pow_pos (n := k) hb
  unfold substitutionAverage
  constructor
  · apply (le_div_iff₀ hB).2
    calc
      _ = ∑ _j : Fin (b ^ k), lo := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ => (hf (iterateSubstitution hb σ k a j)).1
  · apply (div_le_iff₀ hB).2
    calc
      _ ≤ ∑ _j : Fin (b ^ k), hi := Finset.sum_le_sum fun j _ =>
        (hf (iterateSubstitution hb σ k a j)).2
      _ = _ := by simp [nsmul_eq_mul, mul_comm]

theorem substitutionAverage_add (hb : 0 < b) (σ : A → Fin b → A) (r t : Nat)
    (f : A → ℝ) (a : A) :
    substitutionAverage hb σ (r + t) f a =
      substitutionAverage hb σ r (substitutionAverage hb σ t f) a := by
  unfold substitutionAverage
  have he :
      (∑ j : Fin (b ^ (r + t)), f (iterateSubstitution hb σ (r + t) a j)) =
      ∑ i : Fin (b ^ r), ∑ j : Fin (b ^ t),
        f (iterateSubstitution hb σ t (iterateSubstitution hb σ r a i) j) := by
    rw [← Equiv.sum_comp (substitutionBlockIndex b r t)]
    simp only [Fintype.sum_prod_type, iterateSubstitution_add_block]
  have hd (g : Fin (b ^ r) → ℝ) :
      (∑ i, g i / (b ^ t : Nat)) = (∑ i, g i) / (b ^ t : Nat) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [he, hd, div_div]
  simp [pow_add, mul_comm]

private theorem substitutionAverage_common_letter (hb : 0 < b) (σ : A → Fin b → A)
    (r : Nat) (f : A → ℝ) (a c : A) (j : Fin (b ^ r))
    (hj : iterateSubstitution hb σ r a j = c) {lo hi : ℝ} (hf : ∀ d, f d ∈ Icc lo hi) :
    substitutionAverage hb σ r f a ∈
      Icc ((f c + (((b ^ r : Nat) : ℝ) - 1) * lo) / (b ^ r : Nat))
          ((f c + (((b ^ r : Nat) : ℝ) - 1) * hi) / (b ^ r : Nat)) := by
  let B := b ^ r
  have hBn : 0 < B := Nat.pow_pos hb
  have hB : 0 < (B : ℝ) := by exact_mod_cast hBn
  let S : Finset (Fin B) := Finset.univ.erase j
  have hS : (S.card : ℝ) = (B : ℝ) - 1 := by
    have hh := Finset.card_erase_of_mem (Finset.mem_univ j)
    change ((Finset.univ.erase j).card : ℝ) = _
    rw [hh, Finset.card_univ, Fintype.card_fin, Nat.cast_sub hBn]
    norm_num
  have hSum : (∑ i : Fin B, f (iterateSubstitution hb σ r a i)) =
      f c + ∑ i ∈ S, f (iterateSubstitution hb σ r a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hj, add_comm]
  have hl : ((B : ℝ) - 1) * lo ≤ ∑ i ∈ S, f (iterateSubstitution hb σ r a i) := by
    calc
      _ = ∑ _i ∈ S, lo := by simp [nsmul_eq_mul, hS]
      _ ≤ _ := Finset.sum_le_sum fun i _ => (hf _).1
  have hu : (∑ i ∈ S, f (iterateSubstitution hb σ r a i)) ≤ ((B : ℝ) - 1) * hi := by
    calc
      _ ≤ ∑ _i ∈ S, hi := Finset.sum_le_sum fun i _ => (hf _).2
      _ = _ := by simp [nsmul_eq_mul, hS]
  unfold substitutionAverage
  rw [hSum]
  constructor
  · exact div_le_div_of_nonneg_right (add_le_add_left hl _) hB.le
  · exact div_le_div_of_nonneg_right (add_le_add_left hu _) hB.le

/-- Primitivity makes the mean of any bounded letter statistic nearly
independent of the initial letter. The proof uses a common letter in
every primitive block to contract the interval of possible means. -/
theorem primitive_substitutionAverage_center (hb : 0 < b) (σ : A → Fin b → A)
    (hprim : PrimitiveSubstitution hb σ) (c : A)
    (f : A → ℝ) (hf : ∀ d, f d ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : Nat, ∃ ρ : ℝ, ρ ∈ Icc (0 : ℝ) 1 ∧
      ∀ a, |substitutionAverage hb σ k f a - ρ| ≤ ε := by
  obtain ⟨r, hr⟩ := hprim
  let B : ℝ := (b ^ r : Nat)
  let q : ℝ := (B - 1) / B
  have hB : 0 < B := by dsimp [B]; exact_mod_cast Nat.pow_pos (n := r) hb
  have hB' : 1 ≤ B := by dsimp [B]; exact_mod_cast Nat.pow_pos (n := r) hb
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.2 hB') hB.le
  have hq' : q < 1 := (div_lt_one hB).2 (by linarith)
  have hBounds (m : Nat) : ∃ lo hi : ℝ, hi - lo = q ^ m ∧ lo ∈ Icc (0 : ℝ) 1 ∧
      ∀ a, substitutionAverage hb σ (r * m) f a ∈ Icc lo hi := by
    induction m with
    | zero =>
      refine ⟨0, 1, by simp, by simp, fun a => ?_⟩
      exact substitutionAverage_nonempty_bounds hb σ _ f a hf
    | succ m ih =>
      obtain ⟨lo, hi, hgap, hloPrev, hRange⟩ := ih
      let g := substitutionAverage hb σ (r * m) f
      let lo' := (g c + (B - 1) * lo) / B
      let hi' := (g c + (B - 1) * hi) / B
      have hg01 : ∀ a, g a ∈ Icc (0 : ℝ) 1 := fun a =>
        substitutionAverage_nonempty_bounds hb σ _ f a hf
      have hlo : lo' ∈ Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg (add_nonneg (hg01 c).1
          (mul_nonneg (sub_nonneg.2 hB') hloPrev.1)) hB.le, ?_⟩
        apply (div_le_iff₀ hB).2
        have hh := mul_le_mul_of_nonneg_left hloPrev.2 (sub_nonneg.2 hB')
        linarith [(hg01 c).2]
      refine ⟨lo', hi', ?_, hlo, fun a => ?_⟩
      · dsimp [lo', hi']
        rw [← sub_div]
        have he : g c + (B - 1) * hi - (g c + (B - 1) * lo) = (B - 1) * (hi - lo) := by ring
        rw [he, hgap, pow_succ]
        dsimp [q]
        ring
      · obtain ⟨j, hj⟩ := hr a c
        rw [Nat.mul_succ, Nat.add_comm (r * m) r, substitutionAverage_add]
        exact substitutionAverage_common_letter hb σ r g a c j hj hRange
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq'
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨lo, hi, hgap, hlo, hRange⟩ := hBounds m
  refine ⟨r * m, lo, hlo, fun a => ?_⟩
  rw [abs_of_nonneg (sub_nonneg.2 (hRange a).1)]
  have hh := (hRange a).2
  linarith

end Thesis.ThueMorse
