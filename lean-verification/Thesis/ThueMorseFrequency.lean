import Thesis.ThueMorseFourier
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

open Filter Topology
open scoped BigOperators

namespace Thesis.ThueMorse

/-- The number of occurrences of c between i and i+n, with i+n excluded. -/
def letterCount (w : Nat → Nat) (i n c : Nat) : Nat :=
  ∑ j ∈ Finset.range n, if w (i + j) = c then 1 else 0

private theorem letterCount_add (w : Nat → Nat) (i n m c : Nat) :
    letterCount w i (n + m) c = letterCount w i n c + letterCount w (i + n) m c := by
  simp only [letterCount, Finset.sum_range_add, Nat.add_assoc]

private theorem letterCount_le (w : Nat → Nat) (i n c : Nat) : letterCount w i n c ≤ n := by
  unfold letterCount
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (1 : Nat) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> omega
    _ = n := by simp

private noncomputable def discrepancy (b N i n c : Nat) : ℝ :=
  (letterCount (word b N) i n c : ℝ) - (n : ℝ) / N

private theorem discrepancy_add (b N i n m c : Nat) :
    discrepancy b N i (n + m) c =
      discrepancy b N i n c + discrepancy b N (i + n) m c := by
  unfold discrepancy
  rw [letterCount_add, Nat.cast_add, Nat.cast_add, add_div]
  ring

private theorem discrepancy_boundary (b N i n c : Nat) :
    |discrepancy b N i n c| ≤ (n : ℝ) + (n : ℝ) / N := by
  unfold discrepancy
  have hcount := letterCount_le (word b N) i n c
  have he : (letterCount (word b N) i n c : ℝ) ≤ n := by exact_mod_cast hcount
  have hcount0 : (0 : ℝ) ≤ (letterCount (word b N) i n c : ℝ) := by positivity
  have hdiv0 : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem aligned_discrepancy {b N k c : Nat} (hb : 1 < b) (hN : 1 < N) (hc : c < N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {β : ℝ} (hβ : 0 ≤ β)
    (hker : ∀ l : Nat, 0 < l → l < N → ‖digitKernel b (ζ ^ l)‖ ≤ β) (m : Nat) :
    |discrepancy b N (b ^ k * m) (b ^ k) c| ≤ β ^ k := by
  have he : letterCount (word b N) (b ^ k * m) (b ^ k) c =
      blockLetterCount b N k (word b N m) c := by
    unfold letterCount blockLetterCount
    apply Finset.sum_congr rfl
    intro i hi
    rw [word_aligned hb k m i (Finset.mem_range.mp hi)]
  unfold discrepancy
  rw [he, Nat.cast_pow]
  exact block_count_discrepancy hb hN hζ hβ hker k _ c hc

private theorem aligned_run_discrepancy {b N k c : Nat} (hb : 1 < b) (hN : 1 < N) (hc : c < N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {β : ℝ} (hβ : 0 ≤ β)
    (hker : ∀ l : Nat, 0 < l → l < N → ‖digitKernel b (ζ ^ l)‖ ≤ β) (m q : Nat) :
    |discrepancy b N (b ^ k * m) (b ^ k * q) c| ≤ (q : ℝ) * β ^ k := by
  induction q with
  | zero => simp [discrepancy, letterCount]
  | succ q ih =>
    rw [Nat.mul_succ, discrepancy_add, ← Nat.mul_add, Nat.cast_succ, add_mul, one_mul]
    exact (abs_add_le _ _).trans
      (add_le_add ih (aligned_discrepancy hb hN hc hζ hβ hker (m+q)))

/-- Decompose a window into complete aligned b^k blocks and its two ends.
This is the uniform error estimate in thm:dynWb (4). -/
theorem window_discrepancy {b N k c : Nat} (hb : 1 < b) (hN : 1 < N) (hc : c < N)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {β : ℝ} (hβ : 0 ≤ β)
    (hker : ∀ l : Nat, 0 < l → l < N → ‖digitKernel b (ζ ^ l)‖ ≤ β) (i n : Nat) :
    |(letterCount (word b N) i n c : ℝ) - (n : ℝ) / N| ≤
      (n : ℝ) * (β / b)^k + 2 * (b : ℝ)^k + 2 * (b : ℝ)^k / N := by
  let B : Nat := b ^ k
  have hB : 0 < B := by dsimp [B]; exact Nat.pow_pos (by omega)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hβk : 0 ≤ β ^ k := pow_nonneg hβ _
  change |discrepancy b N i n c| ≤ (n : ℝ) * (β / b)^k + 2 * (b : ℝ)^k + 2 * (b : ℝ)^k / N
  rw [div_pow, ← Nat.cast_pow]
  change _ ≤ (n : ℝ) * (β ^ k / (B : ℝ)) + 2 * (B : ℝ) + 2 * (B : ℝ) / N
  rw [mul_div_assoc (2 : ℝ) (B : ℝ) (N : ℝ)]
  by_cases hn : n < B
  · have h1 : (n : ℝ) ≤ B := by exact_mod_cast hn.le
    have h2 := div_le_div_of_nonneg_right h1 hNpos.le
    have h3 : 0 ≤ (n : ℝ) * (β ^ k / (B : ℝ)) := by positivity
    have h4 : 0 ≤ (B : ℝ) / N := by positivity
    linarith only [discrepancy_boundary b N i n c, h1, h2, h3, h4, hBR.le]
  · let d := B - i % B
    let m := i / B + 1
    let q := (n - d) / B
    let r := (n - d) % B
    have hdiv := Nat.mod_add_div i B
    have hmod := Nat.mod_lt i hB
    have hdB : d ≤ B := Nat.sub_le _ _
    have hd : d ≤ n := hdB.trans (Nat.le_of_not_gt hn)
    have hstart : i + d = B * m := by
      change i + (B - i % B) = B * (i / B + 1)
      rw [Nat.mul_succ]
      omega
    have hr : r < B := Nat.mod_lt _ hB
    have hn' : d + (B * q + r) = n := by
      have he := Nat.mod_add_div (n - d) B
      dsimp only [q, r]
      omega
    have hbound : |discrepancy b N i n c| ≤
        ((d : ℝ) + d / N) + (q : ℝ) * β ^ k + ((r : ℝ) + r / N) := by
      conv_lhs => rw [← hn', discrepancy_add, discrepancy_add, hstart]
      calc
        _ ≤ |discrepancy b N i d c| +
            (|discrepancy b N (B * m) (B * q) c| +
              |discrepancy b N (B * m + B * q) r c|) :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
        _ ≤ _ := by
          have h₁ := discrepancy_boundary b N i d c
          have h₂ := aligned_run_discrepancy (k := k) hb hN hc hζ hβ hker m q
          have h₃ := discrepancy_boundary b N (B * m + B * q) r c
          change |discrepancy b N (B * m) (B * q) c| ≤ (q : ℝ) * β ^ k at h₂
          linarith
    have hq : (q : ℝ) ≤ (n : ℝ) / (B : ℝ) := by
      apply (le_div_iff₀ hBR).2
      have hh : B * q ≤ n := by omega
      rw [mul_comm]
      exact_mod_cast hh
    have hq' : (q : ℝ) * β ^ k ≤ (n : ℝ) * (β ^ k / (B : ℝ)) := by
      calc
        _ ≤ (n : ℝ) / (B : ℝ) * β ^ k := mul_le_mul_of_nonneg_right hq hβk
        _ = _ := by ring
    have he₁ : (d : ℝ) ≤ B := by exact_mod_cast hdB
    have he₂ : (r : ℝ) ≤ B := by exact_mod_cast hr.le
    have he₃ := div_le_div_of_nonneg_right he₁ hNpos.le
    have he₄ := div_le_div_of_nonneg_right he₂ hNpos.le
    linarith only [hbound, hq', he₁, he₂, he₃, he₄]

/-- Choose the exponent so that b^k ≤ √n < b^(k+1), in the integer form
needed for the error bound. This exponent tends to infinity. -/
private theorem sqrt_exponent_bounds {b n : Nat} (hb : 1 < b) (hn : 0 < n) :
    let k := Nat.log b n.sqrt
    (b ^ k) ^ 2 ≤ n ∧ n < (b ^ (k + 1)) ^ 2 := by
  dsimp only
  refine ⟨Nat.le_sqrt'.1 (Nat.pow_log_le_self b (Nat.sqrt_pos.2 hn).ne'), ?_⟩
  exact Nat.sqrt_lt'.1 (Nat.lt_pow_succ_log_self hb _)

/-- The letter discrepancy is o(n), uniformly over the initial
position and the choice of letter. -/
theorem uniform_letter_discrepancy_o {b N : Nat} (hb : 1 < b) (hN : 1 < N) :
    ∀ ε : ℝ, 0 < ε → ∃ M : Nat, ∀ n ≥ M, ∀ i c : Nat, c < N →
      |(letterCount (word b N) i n c : ℝ) - (n : ℝ) / N| < ε * (n : ℝ) := by
  intro ε hε
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hz : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N (by omega)
  obtain ⟨β, hβ, hβb, hker⟩ := exists_digit_kernel_bound hb hN hz
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := zero_lt_one.trans hbR
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let C : ℝ := 2 + 2 / N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbInv : (1 : ℝ) / b < 1 := (div_lt_one hb0).2 hbR
  have hβq : β / (b : ℝ) < 1 := (div_lt_one hb0).2 hβb
  have ht₁ := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hβ hb0.le) hβq
  have ht₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hbInv
  have hlim := ht₁.add (ht₂.const_mul C)
  simp only [mul_zero, add_zero] at hlim
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))
  refine ⟨(b ^ K) ^ 2, fun n hn i c hc => ?_⟩
  have hn0 : 0 < n := (Nat.pow_pos (Nat.pow_pos (by omega))).trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let k := Nat.log b n.sqrt
  have hk : K ≤ k := Nat.le_log_of_pow_le hb (Nat.le_sqrt'.2 hn)
  have hbase := (sqrt_exponent_bounds hb hn0).1
  have hbaseR : (((b : ℝ) ^ k) ^ 2) ≤ n := by exact_mod_cast hbase
  have hB : 0 < (b : ℝ) ^ k := pow_pos hb0 _
  have hfrac : (b : ℝ) ^ k / n ≤ (1 / (b : ℝ)) ^ k := by
    rw [div_pow, one_pow]
    apply (div_le_div_iff₀ hnR hB).2
    simpa only [one_mul, pow_two] using hbaseR
  have hsum : (2 * (b : ℝ) ^ k + 2 * (b : ℝ) ^ k / N) / (n : ℝ) =
      C * ((b : ℝ) ^ k / n) := by dsimp [C]; ring
  have hsmall := hK k hk
  have herror := window_discrepancy (k := k) hb hN hc hz hβ hker i n
  apply (div_lt_iff₀ hnR).1
  apply (div_le_div_of_nonneg_right herror hnR.le).trans_lt
  rw [add_assoc, add_div, mul_comm (n : ℝ), mul_div_cancel_right₀ _ hnR.ne', hsum]
  exact (add_le_add_left (mul_le_mul_of_nonneg_left hfrac hC) _).trans_lt hsmall

end Thesis.ThueMorse
