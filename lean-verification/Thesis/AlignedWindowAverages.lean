import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace Thesis.ThueMorse

/-- Sum a statistic over n consecutive starting positions. -/
def windowSum (f : Nat → ℝ) (i n : Nat) : ℝ :=
  ∑ j ∈ Finset.range n, f (i + j)

theorem windowSum_add (f : Nat → ℝ) (i n m : Nat) :
    windowSum f i (n + m) = windowSum f i n + windowSum f (i + n) m := by
  simp only [windowSum, Finset.sum_range_add, Nat.add_assoc]

theorem windowSum_mul (f : Nat → ℝ) (i B q : Nat) :
    windowSum f i (B * q) = ∑ j ∈ Finset.range q, windowSum f (i + B * j) B := by
  induction q with
  | zero => simp [windowSum]
  | succ q ih => rw [Nat.mul_succ, windowSum_add, ih, Finset.sum_range_succ]

theorem windowSum_interval (f : Nat → ℝ) {l h : ℝ} (hf : ∀ j, l ≤ f j ∧ f j ≤ h) (i n : Nat) :
    (n : ℝ) * l ≤ windowSum f i n ∧ windowSum f i n ≤ (n : ℝ) * h := by
  unfold windowSum
  constructor
  · simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.range n) fun j _ => (hf (i + j)).1)
  · simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.range n) fun j _ => (hf (i + j)).2)

private theorem windowSum_run_bound (f : Nat → ℝ) (D : Nat) (ρ δ : ℝ)
    (h : ∀ m, |windowSum f (D * m) D - (D : ℝ) * ρ| ≤ (D : ℝ) * δ)
    (m q : Nat) :
    |windowSum f (D * m) (D * q) - ((D * q : Nat) : ℝ) * ρ| ≤
      ((D * q : Nat) : ℝ) * δ := by
  induction q with
  | zero => simp [windowSum]
  | succ q ih =>
    rw [Nat.mul_succ, windowSum_add, ← Nat.mul_add, Nat.cast_add, add_mul, add_mul]
    rw [show windowSum f (D * m) (D * q) + windowSum f (D * (m + q)) D -
      (((D * q : Nat) : ℝ) * ρ + (D : ℝ) * ρ) =
        (windowSum f (D * m) (D * q) - ((D * q : Nat) : ℝ) * ρ) +
        (windowSum f (D * (m + q)) D - (D : ℝ) * ρ) by ring]
    exact (abs_add_le _ _).trans (add_le_add ih (h (m + q)))

/-- Control on a common center for aligned blocks transfers to windows at
arbitrary starting positions. For the chosen length the two ends have
total length exactly one block. -/
theorem window_avg_of_aligned (f : Nat → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1)
    {D : Nat} (hD : 0 < D) {ρ δ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hδ : 0 ≤ δ)
    (h : ∀ m, |windowSum f (D * m) D - (D : ℝ) * ρ| ≤ (D : ℝ) * δ)
    (i q : Nat) :
    |windowSum f i (D * (q + 1)) / ((D * (q + 1) : Nat) : ℝ) - ρ| ≤
      δ + 1 / (q + 1 : Nat) := by
  let d := D - i % D
  let m := i / D + 1
  have hd : d ≤ D := Nat.sub_le _ _
  have hstart : i + d = D * m := by
    have hi := Nat.mod_add_div i D
    have hj := Nat.mod_lt i hD
    dsimp [d, m]
    rw [Nat.mul_succ]
    omega
  have hsplit : D * (q + 1) = d + (D * q + (D - d)) := by rw [Nat.mul_succ]; omega
  have hEdge (j a : Nat) : |windowSum f j a - (a : ℝ) * ρ| ≤ a := by
    obtain ⟨hl, hu⟩ := windowSum_interval f hf j a
    have h0 : 0 ≤ (a : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ.1
    have h1 : (a : ℝ) * ρ ≤ (a : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hρ.2 (Nat.cast_nonneg _)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have htail : ((d : ℝ) + ((D - d : Nat) : ℝ)) = (D : ℝ) := by
    rw [Nat.cast_sub hd]; ring
  have htotal : ((D * (q + 1) : Nat) : ℝ) =
      (d : ℝ) + ((((D * q : Nat) : ℝ)) + ((D - d : Nat) : ℝ)) := by
    exact_mod_cast hsplit
  have hsum : |windowSum f i (D * (q + 1)) - ((D * (q + 1) : Nat) : ℝ) * ρ| ≤
      ((D * q : Nat) : ℝ) * δ + (D : ℝ) := by
    have hmid := windowSum_run_bound f D ρ δ h m q
    have hleft := hEdge i d
    have hright := hEdge (D * m + D * q) (D - d)
    rw [htotal]
    conv_lhs => rw [hsplit, windowSum_add, hstart, windowSum_add]
    let u := windowSum f i d - (d : ℝ) * ρ
    let v := windowSum f (D * m) (D * q) - ((D * q : Nat) : ℝ) * ρ
    let z := windowSum f (D * m + D * q) (D - d) - ((D - d : Nat) : ℝ) * ρ
    have he : windowSum f i d + (windowSum f (D * m) (D * q) +
        windowSum f (D * m + D * q) (D - d)) -
        ((d : ℝ) + (((D * q : Nat) : ℝ) + ((D - d : Nat) : ℝ))) * ρ =
        u + (v + z) := by dsimp [u, v, z]; ring
    rw [he]
    have hb := (abs_add_le u (v + z)).trans
      (add_le_add_left (abs_add_le v z) _)
    change |u| ≤ (d : ℝ) at hleft
    change |v| ≤ ((D * q : Nat) : ℝ) * δ at hmid
    change |z| ≤ ((D - d : Nat) : ℝ) at hright
    linarith
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hn : 0 < ((D * (q + 1) : Nat) : ℝ) := by exact_mod_cast Nat.mul_pos hD (Nat.succ_pos q)
  rw [div_sub' hn.ne', abs_div, abs_of_nonneg hn.le]
  apply (div_le_iff₀ hn).2
  refine hsum.trans ?_
  push_cast
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have he : (δ + 1 / ((q : ℝ) + 1)) * ((D : ℝ) * ((q : ℝ) + 1)) =
      (D : ℝ) * q * δ + D + (D : ℝ) * δ := by field_simp; ring
  rw [he]
  exact le_add_of_nonneg_right (by positivity)

end Thesis.ThueMorse
