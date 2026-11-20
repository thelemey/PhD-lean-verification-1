import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

open Filter Topology

namespace Thesis.Recurrence

/-- A first-order difference with a root of norm less than one is stable:
if its forcing term tends to zero, so does the sequence. -/
theorem tendsto_zero_of_difference {u : Nat → ℂ} {z : ℂ} (hz : ‖z‖ < 1)
    (h : Tendsto (fun n => u (n + 1) - z * u n) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let q := ‖z‖
  let e := ε / 2
  have hq : 0 ≤ q := norm_nonneg _
  have he : 0 < e := by dsimp [e]; linarith
  have hδ : 0 < (1 - q) * e := mul_pos (sub_pos.mpr hz) he
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ((1 - q) * e) hδ
  have hstep (n : Nat) (hn : N ≤ n) : ‖u (n + 1)‖ ≤ q * ‖u n‖ + (1 - q) * e := by
    have hb := hN n hn
    rw [dist_zero_right] at hb
    calc
      ‖u (n + 1)‖ = ‖z * u n + (u (n + 1) - z * u n)‖ := by ring_nf
      _ ≤ _ := by
        have hi := norm_add_le (z * u n) (u (n + 1) - z * u n)
        rw [norm_mul] at hi
        exact hi.trans (add_le_add_left hb.le _)
  have hbd (k : Nat) : ‖u (N + k)‖ ≤ q ^ k * ‖u N‖ + e := by
    induction k with
    | zero =>
      simpa only [Nat.add_zero, pow_zero, one_mul] using le_add_of_nonneg_right he.le
    | succ k ih =>
      have h₁ := hstep (N + k) (by omega)
      have h₂ := mul_le_mul_of_nonneg_left ih hq
      rw [show N + (k + 1) = N + k + 1 by omega, pow_succ]
      linarith only [h₁, h₂, show q * (q ^ k * ‖u N‖ + e) + (1 - q) * e =
        q ^ k * q * ‖u N‖ + e by ring]
  have hpow : Tendsto (fun k : Nat => q ^ k * ‖u N‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq hz).mul_const ‖u N‖
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hpow.eventually (gt_mem_nhds he))
  refine ⟨N + K, fun n hn => ?_⟩
  have hk : K ≤ n - N := by omega
  have hbound := hbd (n - N)
  rw [Nat.add_sub_of_le (show N ≤ n by omega)] at hbound
  have hsmall := hK _ hk
  rw [dist_zero_right]
  dsimp [e] at hbound hsmall
  linarith

end Thesis.Recurrence
