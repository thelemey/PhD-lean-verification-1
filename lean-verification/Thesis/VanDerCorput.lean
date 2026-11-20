import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators

namespace Thesis.VanDerCorput

/-- The lag-`r` correlation of a segment of length `N`, indexed from zero. -/
noncomputable def correlation (u : Nat → ℂ) (N r : Nat) : ℂ :=
  ∑ n ∈ range (N - r), u (n + r) * (starRingEnd ℂ) (u n)

/-- The value of the zero-extended segment at the shifted index (m-j).
The first guard is needed because subtraction on natural numbers truncates. -/
def padded (u : Nat → ℂ) (N m j : Nat) : ℂ :=
  if j ≤ m ∧ m - j < N then u (m - j) else 0

private theorem sum_shifted_supported {G : Type*} [AddCommMonoid G]
    (f : Nat → G) (start len M : Nat) (hM : 0 < len → start + len ≤ M)
    (hf : ∀ m < M, ¬ (start ≤ m ∧ m < start + len) → f m = 0) :
    (∑ m ∈ range M, f m) = ∑ n ∈ range len, f (start + n) := by
  let e : Nat ↪ Nat := ⟨fun n => start + n, fun _ _ h => Nat.add_left_cancel h⟩
  have hmem (m : Nat) : m ∈ (range len).map e ↔ start ≤ m ∧ m < start + len := by
    simp only [Finset.mem_map, Finset.mem_range, e, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨n, hn, rfl⟩
      omega
    · intro h
      exact ⟨m - start, by omega, by omega⟩
  calc
    _ = ∑ m ∈ (range len).map e, f m := by
      symm
      apply Finset.sum_subset
      · intro m hm
        have := (hmem m).1 hm
        exact Finset.mem_range.mpr (by have := hM (by omega); omega)
      · intro m hm hn
        exact hf m (Finset.mem_range.mp hm) (fun h => hn ((hmem m).2 h))
    _ = _ := Finset.sum_map _ _ _

private theorem sum_padded (u : Nat → ℂ) (N H j : Nat) (hj : j < H) :
    (∑ m ∈ range (N + H - 1), padded u N m j) = ∑ n ∈ range N, u n := by
  rw [sum_shifted_supported (fun m => padded u N m j) j N (N + H - 1)
    (by omega) (by
      intro m _ h
      change padded u N m j = 0
      unfold padded
      rw [if_neg]
      omega)]
  apply Finset.sum_congr rfl
  intro n hn
  have h := Finset.mem_range.mp hn
  simp [padded, h]

private theorem sum_padded_norm_sq (u : Nat → ℂ) (hu : ∀ n, ‖u n‖ = 1)
    (N H j : Nat) (hj : j < H) :
    (∑ m ∈ range (N + H - 1), ‖padded u N m j‖ ^ 2) = (N : ℝ) := by
  rw [sum_shifted_supported (fun m => ‖padded u N m j‖ ^ 2) j N (N + H - 1)
    (by omega) (by
      intro m _ h
      have hpad : padded u N m j = 0 := by unfold padded; rw [if_neg]; omega
      simp [hpad])]
  apply (Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) ?_).trans
  · simp
  · intro n hn
    simp [padded, Finset.mem_range.mp hn, hu]

private theorem sum_padded_cross (u : Nat → ℂ) (N H j k : Nat) (hjk : j < k)
    (hk : k < H) :
    (∑ m ∈ range (N + H - 1),
      (padded u N m j * (starRingEnd ℂ) (padded u N m k)).re) =
      (correlation u N (k - j)).re := by
  rw [sum_shifted_supported (fun m =>
      (padded u N m j * (starRingEnd ℂ) (padded u N m k)).re)
    k (N - (k - j)) (N + H - 1) (by omega) (by
      intro m _ h
      by_cases hm : k ≤ m
      · have hj : ¬ (j ≤ m ∧ m - j < N) := by omega
        simp [padded, hj]
      · simp [padded, hm])]
  rw [correlation, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have h := Finset.mem_range.mp hn
  have hnj : k + n - j < N := by omega
  have hnk : n < N := by omega
  have he : k + n - j = n + (k - j) := by omega
  have hj : j ≤ k + n := by omega
  have hk' : k ≤ k + n := by omega
  have hes : k + n - k = n := by omega
  have hnk' : k + n - k < N := by omega
  rw [padded, padded, if_pos ⟨hj, hnj⟩, if_pos ⟨hk', hnk'⟩, he, hes]

private theorem sq_norm_sum (v : Nat → ℂ) (H : Nat) :
    ‖∑ j ∈ range H, v j‖ ^ 2 =
      (∑ j ∈ range H, ‖v j‖ ^ 2) +
        2 * ∑ k ∈ range H, ∑ j ∈ range k, (v j * (starRingEnd ℂ) (v k)).re := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, Complex.sq_norm, Complex.normSq_add,
      ← Complex.sq_norm, ← Complex.sq_norm, ih, Finset.sum_mul, Complex.re_sum]
    rw [Finset.sum_range_succ (fun j => ‖v j‖ ^ 2),
      Finset.sum_range_succ (fun k => ∑ j ∈ range k, (v j * (starRingEnd ℂ) (v k)).re)]
    ring

private theorem upper_triangle_by_lag (f : Nat → ℝ) (H : Nat) :
    (∑ k ∈ range H, ∑ j ∈ range k, f (k - j)) =
      ∑ r ∈ range (H - 1), ((H - (r + 1) : Nat) : ℝ) * f (r + 1) := by
  have hreflect (k : Nat) :
      (∑ j ∈ range k, f (k - j)) = ∑ r ∈ range k, f (r + 1) := by
    rw [← Finset.sum_range_reflect (fun j => f (k - j)) k]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    congr 1
    omega
  have hx (k : Nat) (hk : k ∈ range H) :
      (∑ r ∈ range k, f (r + 1)) =
        ∑ r ∈ range (H - 1), if r < k then f (r + 1) else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  calc
    _ = ∑ k ∈ range H, ∑ r ∈ range (H - 1), if r < k then f (r + 1) else 0 := by
      refine Finset.sum_congr rfl fun k hk => (hreflect k).trans (hx k hk)
    _ = ∑ r ∈ range (H - 1), ∑ k ∈ range H, if r < k then f (r + 1) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hset : (range H).filter (fun k => r < k) = Ico (r + 1) H := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [hset, Nat.card_Ico]

private theorem window_energy (u : Nat → ℂ) (hu : ∀ n, ‖u n‖ = 1) (N H : Nat) :
    (∑ m ∈ range (N + H - 1), ‖∑ j ∈ range H, padded u N m j‖ ^ 2) =
      (H : ℝ) * N + 2 * ∑ r ∈ range (H - 1),
        ((H - (r + 1) : Nat) : ℝ) * (correlation u N (r + 1)).re := by
  simp only [sq_norm_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdiag :
      (∑ m ∈ range (N + H - 1), ∑ j ∈ range H, ‖padded u N m j‖ ^ 2) =
        (H : ℝ) * N := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j ∈ range H, (N : ℝ) := by
        exact Finset.sum_congr rfl (fun j hj => sum_padded_norm_sq u hu N H j (Finset.mem_range.mp hj))
      _ = _ := by simp [nsmul_eq_mul]
  rw [hdiag]
  have hcross :
      (∑ m ∈ range (N + H - 1), ∑ k ∈ range H, ∑ j ∈ range k,
        (padded u N m j * (starRingEnd ℂ) (padded u N m k)).re) =
      ∑ r ∈ range (H - 1), ((H - (r + 1) : Nat) : ℝ) * (correlation u N (r + 1)).re := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ k ∈ range H, ∑ j ∈ range k, (correlation u N (k - j)).re := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j hj =>
          sum_padded_cross u N H j k (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
      _ = _ := upper_triangle_by_lag (fun r => (correlation u N r).re) H
  rw [hcross]

/-- The finite shift-and-square inequality used in `lem:logfact`.
Here the index `r` runs from zero to `H-2`, so its lag is `r+1`.
The real parts are kept in the conclusion, before bounding them by norms. -/
theorem finite_shift_square (u : Nat → ℂ) (hu : ∀ n, ‖u n‖ = 1) (N H : Nat) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ range N, u n‖ ^ 2 ≤
      ((N + H - 1 : Nat) : ℝ) * ((H : ℝ) * N +
        2 * ∑ r ∈ range (H - 1),
          ((H - (r + 1) : Nat) : ℝ) * (correlation u N (r + 1)).re) := by
  let win : Nat → ℂ := fun m => ∑ j ∈ range H, padded u N m j
  have hsum : (∑ m ∈ range (N + H - 1), win m) = (H : ℂ) * ∑ n ∈ range N, u n := by
    unfold win
    rw [Finset.sum_comm]
    calc
      _ = ∑ _ ∈ range H, ∑ n ∈ range N, u n := by
        exact Finset.sum_congr rfl fun j hj => sum_padded u N H j (Finset.mem_range.mp hj)
      _ = _ := by simp [nsmul_eq_mul]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (range (N + H - 1))
    (fun _ => (1 : ℝ)) (fun m => ‖win m‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hc
  have ht := norm_sum_le (range (N + H - 1)) win
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  rw [hsum, Complex.norm_mul, Complex.norm_natCast, mul_pow] at hs
  exact hs.trans (hc.trans_eq (congrArg (fun z : ℝ => ((N + H - 1 : Nat) : ℝ) * z)
    (window_energy u hu N H)))

end Thesis.VanDerCorput
