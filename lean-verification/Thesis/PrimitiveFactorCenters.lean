import Thesis.PrimitiveSubstitutionAverages
import Thesis.AlignedWindowAverages
import Thesis.WordCylinderMeasures

open Set
open scoped BigOperators

namespace Thesis.ThueMorse

variable {A : Type*} {b : Nat}

private noncomputable def factorHit (w : Nat → A) {k : Nat} (u : Fin k → A) (i : Nat) : ℝ := by
  classical
  exact if window w k i = u then 1 else 0

private theorem factorHit_bounds (w : Nat → A) {k : Nat} (u : Fin k → A) (i : Nat) :
    0 ≤ factorHit w u i ∧ factorHit w u i ≤ 1 := by
  unfold factorHit
  split_ifs <;> norm_num

private theorem factorHit_congr {w v : Nat → A} {k i j : Nat} (u : Fin k → A)
    (h : window w k i = window v k j) : factorHit w u i = factorHit v u j := by
  unfold factorHit
  rw [h]

private theorem factorFrequency_eq_windowSum (w : Nat → A) {k : Nat} (u : Fin k → A) (i n : Nat) :
    factorFrequency w u i n = windowSum (factorHit w u) i n / (n : ℝ) := by
  classical
  simp only [factorFrequency, Finset.natCast_card_filter, windowSum, factorHit]

private def extendedBlock (hb : 0 < b) (σ : A → Fin b → A) (t : Nat) (a : A) (j : Nat) : A :=
  if hj : j < b ^ t then iterateSubstitution hb σ t a ⟨j, hj⟩ else a

private noncomputable def interiorStatistic (hb : 0 < b) (σ : A → Fin b → A)
    (t : Nat) {k : Nat} (u : Fin k → A) (a : A) : ℝ :=
  windowSum (factorHit (extendedBlock hb σ t a) u) 0 (b ^ t - k) / ((b ^ t : Nat) : ℝ)

private theorem interiorStatistic_bounds (hb : 0 < b) (σ : A → Fin b → A)
    (t : Nat) {k : Nat} (u : Fin k → A) (a : A) :
    interiorStatistic hb σ t u a ∈ Icc (0 : ℝ) 1 := by
  have hB : 0 < ((b ^ t : Nat) : ℝ) := by exact_mod_cast Nat.pow_pos (n := t) hb
  obtain ⟨hl, hu⟩ :=
    windowSum_interval _ (factorHit_bounds (extendedBlock hb σ t a) u) 0 (b ^ t - k)
  unfold interiorStatistic
  refine ⟨div_nonneg (by linarith) hB.le, (div_le_iff₀ hB).2 ?_⟩
  have hcast : ((b ^ t - k : Nat) : ℝ) ≤ ((b ^ t : Nat) : ℝ) := by
    exact_mod_cast Nat.sub_le (b ^ t) k
  linarith

/-- The internal starts are determined by the substitution block.
At most k of the remaining starts are lost at its right boundary. -/
private theorem fine_block_error (hb : 0 < b) (σ : A → Fin b → A) (w : Nat → A)
    (hw : SubstitutionFixedWord σ w) (t : Nat) {k : Nat} (u : Fin k → A)
    (hk : k ≤ b ^ t) (m : Nat) :
    |windowSum (factorHit w u) (b ^ t * m) (b ^ t) -
      ((b ^ t : Nat) : ℝ) * interiorStatistic hb σ t u (w m)| ≤ (k : ℝ) := by
  let B := b ^ t
  have hB : (0 : ℝ) < B := by dsimp [B]; exact_mod_cast Nat.pow_pos (n := t) hb
  have he : windowSum (factorHit w u) (B * m) (B - k) =
      windowSum (factorHit (extendedBlock hb σ t (w m)) u) 0 (B - k) := by
    unfold windowSum
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < B - k := Finset.mem_range.1 hj
    have hwin : window w k (B * m + j) = window (extendedBlock hb σ t (w m)) k j := by
      funext l
      have hl : j + l.val < b ^ t := by change j + l.val < B; have := l.isLt; omega
      simp only [window, extendedBlock, dif_pos hl]
      rw [Nat.add_assoc]
      exact fixedWord_iterate_block hb σ w hw t m ⟨j + l.val, hl⟩
    apply factorHit_congr
    simpa only [Nat.zero_add] using hwin
  have he' : (B : ℝ) * interiorStatistic hb σ t u (w m) =
      windowSum (factorHit w u) (B * m) (B - k) := by
    unfold interiorStatistic
    change (B : ℝ) * (_ / (B : ℝ)) = _
    rw [mul_div_cancel₀ _ hB.ne', he]
  change |windowSum (factorHit w u) (B * m) B - (B : ℝ) *
    interiorStatistic hb σ t u (w m)| ≤ (k : ℝ)
  have hs : windowSum (factorHit w u) (B * m) B =
      windowSum (factorHit w u) (B * m) (B - k) +
        windowSum (factorHit w u) (B * m + (B - k)) k := by
    have hk' : k ≤ B := hk
    simpa only [Nat.sub_add_cancel hk'] using windowSum_add (factorHit w u) (B * m) (B - k) k
  rw [he', hs, add_sub_cancel_left]
  obtain ⟨hl, hu⟩ := windowSum_interval _ (factorHit_bounds w u) (B * m + (B - k)) k
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem coarse_block_error (hb : 0 < b) (σ : A → Fin b → A) (w : Nat → A)
    (hw : SubstitutionFixedWord σ w) (s t : Nat) {k : Nat} (u : Fin k → A)
    (hk : k ≤ b ^ t) (m : Nat) :
    let D := b ^ (s + t)
    |windowSum (factorHit w u) (D * m) D -
      (D : ℝ) * substitutionAverage hb σ s (interiorStatistic hb σ t u) (w m)| ≤
        ((b ^ s : Nat) : ℝ) * (k : ℝ) := by
  let B := b ^ t
  let Q := b ^ s
  let d := interiorStatistic hb σ t u
  have hQ : (0 : ℝ) < Q := by dsimp [Q]; exact_mod_cast Nat.pow_pos (n := s) hb
  have hD : b ^ (s + t) = B * Q := by simp [pow_add, B, Q, Nat.mul_comm]
  dsimp only
  rw [hD, windowSum_mul, ← Fin.sum_univ_eq_sum_range]
  have hError (j : Fin Q) :
      |windowSum (factorHit w u) (B * Q * m + B * j.val) B -
        (B : ℝ) * d (iterateSubstitution hb σ s (w m) j)| ≤ (k : ℝ) := by
    have he : B * Q * m + B * j.val = B * (Q * m + j.val) := by ring
    rw [he, ← fixedWord_iterate_block hb σ w hw s m j]
    exact fine_block_error hb σ w hw t u hk (Q * m + j.val)
  have hS : ((B * Q : Nat) : ℝ) * substitutionAverage hb σ s d (w m) =
      ∑ j : Fin Q, (B : ℝ) * d (iterateSubstitution hb σ s (w m) j) := by
    unfold substitutionAverage
    change ((B * Q : Nat) : ℝ) * ((∑ j : Fin Q, d (iterateSubstitution hb σ s (w m) j)) /
      (Q : ℝ)) = _
    rw [Nat.cast_mul, mul_assoc, mul_div_cancel₀ _ hQ.ne', Finset.mul_sum]
  change |(∑ j : Fin Q, windowSum (factorHit w u) (B * Q * m + B * j.val) B) -
    ((B * Q : Nat) : ℝ) * substitutionAverage hb σ s d (w m)| ≤ (Q : ℝ) * (k : ℝ)
  rw [hS, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin Q, |windowSum (factorHit w u) (B * Q * m + B * j.val) B -
        (B : ℝ) * d (iterateSubstitution hb σ s (w m) j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin Q, (k : ℝ) := Finset.sum_le_sum fun j _ => hError j
    _ = _ := by simp [nsmul_eq_mul]

variable [TopologicalSpace A] [DiscreteTopology A]

/-- In a primitive constant-length fixed word, long factor frequencies
can be uniformly approximated by a common center. Boundary starts are
controlled separately from the primitive mixing of the internal counts. -/
theorem primitive_factor_frequency_centers {b : Nat} (hb : 1 < b) (σ : A → Fin b → A) (w : Nat → A)
    (hprim : PrimitiveSubstitution (Nat.zero_lt_one.trans hb) σ)
    (hw : SubstitutionFixedWord σ w) :
    ∀ k (u : Fin k → A) ε, 0 < ε → ∃ n : Nat, 0 < n ∧ ∃ ρ : ℝ,
      ∀ x ∈ wordOrbitClosure w, |factorFrequency x u 0 n - ρ| ≤ ε := by
  intro k u ε hε
  have hb0 := Nat.zero_lt_one.trans hb
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbR : 1 < (b : ℝ) := by exact_mod_cast hb
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hbR).eventually_ge_atTop
    (max (k : ℝ) ((k : ℝ) / δ))).exists
  have htk : k ≤ b ^ t := by exact_mod_cast (le_max_left _ _).trans ht
  have htδ : (k : ℝ) ≤ δ * ((b ^ t : Nat) : ℝ) := by
    rw [mul_comm, Nat.cast_pow]
    exact (div_le_iff₀ hδ).1 ((le_max_right _ _).trans ht)
  let g := interiorStatistic hb0 σ t u
  obtain ⟨s, ρ, hρ, hmix⟩ :=
    primitive_substitutionAverage_center hb0 σ hprim (w 0) g
      (interiorStatistic_bounds hb0 σ t u) hδ
  let D := b ^ (s + t)
  have hDn : 0 < D := Nat.pow_pos hb0
  have hD : (0 : ℝ) < D := by exact_mod_cast hDn
  have hcenter (m : Nat) :
      |windowSum (factorHit w u) (D * m) D - (D : ℝ) * ρ| ≤ (D : ℝ) * (2 * δ) := by
    have he := coarse_block_error hb0 σ w hw s t u htk m
    let z := substitutionAverage hb0 σ s g (w m)
    change |windowSum (factorHit w u) (D * m) D - (D : ℝ) * z| ≤
      ((b ^ s : Nat) : ℝ) * (k : ℝ) at he
    have hr : ((b ^ s : Nat) : ℝ) * (k : ℝ) ≤ (D : ℝ) * δ := by
      have hl := mul_le_mul_of_nonneg_left htδ (Nat.cast_nonneg (b ^ s) : (0 : ℝ) ≤ ((b ^ s : Nat) : ℝ))
      simp only [D, pow_add, Nat.cast_mul]
      exact hl.trans_eq (by ring)
    have hm : |(D : ℝ) * z - (D : ℝ) * ρ| ≤ (D : ℝ) * δ := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hD.le]
      exact mul_le_mul_of_nonneg_left (hmix (w m)) hD.le
    calc
      _ ≤ |windowSum (factorHit w u) (D * m) D - (D : ℝ) * z| + |(D : ℝ) * z - (D : ℝ) * ρ| :=
        abs_sub_le _ _ _
      _ ≤ _ := by linarith
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / δ)
  have hq' : (1 : ℝ) / (q + 1 : Nat) ≤ δ := by
    have hq'' : 0 < ((q + 1 : Nat) : ℝ) := by positivity
    apply (div_le_iff₀ hq'').2
    have hh := (div_lt_iff₀ hδ).1 hq
    push_cast
    nlinarith
  let n := D * (q + 1)
  refine ⟨n, Nat.mul_pos hDn (Nat.succ_pos _), ρ, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := window_of_orbitClosure hx (n + k) 0
  have htransfer : factorFrequency x u 0 n = factorFrequency w u i n := by
    rw [factorFrequency_eq_windowSum, factorFrequency_eq_windowSum]
    congr 1
    unfold windowSum
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hwin : window x k j = window w k (i + j) := by
      funext l
      have hl : j + l.val < n + k := by have := l.isLt; omega
      have he := congrFun hi ⟨j + l.val, hl⟩
      simpa only [window, Nat.zero_add, Nat.add_assoc] using he.symm
    apply factorHit_congr
    simpa only [Nat.zero_add] using hwin
  rw [htransfer, factorFrequency_eq_windowSum]
  have h := window_avg_of_aligned (factorHit w u) (factorHit_bounds w u) hDn hρ
    (by positivity : 0 ≤ 2 * δ) hcenter i q
  change |windowSum (factorHit w u) i n / (n : ℝ) - ρ| ≤ ε
  exact h.trans (by dsimp [δ] at hq' ⊢; linarith)

end Thesis.ThueMorse
