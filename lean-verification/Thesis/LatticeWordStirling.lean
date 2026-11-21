import Thesis.LatticeWord
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

open Filter Topology
open scoped Real

namespace Thesis.LatticeWord

/-- The Pascal recursion already used in `newprove` is the binomial
coefficient of mathlib. -/
theorem choose_eq_natChoose : ∀ n k, choose n k = n.choose k
  | _, 0 => by simp
  | 0, k + 1 => by simp [choose]
  | n + 1, k + 1 => by
    rw [choose, Nat.choose_succ_succ', choose_eq_natChoose n k,
      choose_eq_natChoose n (k + 1)]

private theorem length_diagonal_factorial (n : Nat) (hn : 0 < n) :
    ((word n n).length : ℝ) = (Nat.factorial (2 * n) : ℝ) / (Nat.factorial n : ℝ) ^ 2 := by
  have hc := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega, Nat.mul_assoc, ← pow_two] at hc
  rw [length_word n n (by omega), ← two_mul, choose_eq_natChoose]
  apply (eq_div_iff (pow_ne_zero _ (by positivity : (Nat.factorial n : ℝ) ≠ 0))).2
  exact_mod_cast hc

/-- The normalized factorial in Stirling's formula:
(n!/(\sqrt{2n}(n/e)^n)). The normalization and the limit premise
are kept separate from the central-binomial calculation. -/
noncomputable def stirlingRatio (n : Nat) : ℝ :=
  (Nat.factorial n : ℝ) / (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n)

private theorem log_stirling_ratio (n : Nat) (hn : 0 < n) :
    Real.log (stirlingRatio n) =
      Real.log (Nat.factorial n) - 1 / 2 * Real.log (2 * (n : ℝ)) -
        (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold stirlingRatio
  rw [Real.log_div, Real.log_mul, Real.log_sqrt, Real.log_pow] <;> try positivity
  ring

/-- The exact logarithmic consequence of inserting Stirling's normalized
factorials into the central binomial coefficient. -/
theorem log_diagonal_stirling (n : Nat) (hn : 0 < n) :
    Real.log (word n n).length =
      2 * (n : ℝ) * Real.log 2 +
        (Real.log (stirlingRatio (2 * n)) - 2 * Real.log (stirlingRatio n)) -
        Real.log (n : ℝ) / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have h2f : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by positivity
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos _).ne'
  have h2n : (2 * (n : ℝ)) ≠ 0 := (mul_pos (by norm_num) hnR).ne'
  rw [length_diagonal_factorial n hn, Real.log_div h2f (pow_ne_zero _ hnf), Real.log_pow]
  have hs1 := log_stirling_ratio n hn
  have hs2 := log_stirling_ratio (2 * n) (by omega)
  push_cast at hs2
  rw [Real.log_div h2n he, Real.log_mul two_ne_zero hnR.ne'] at hs2
  rw [Real.log_div hnR.ne' he] at hs1
  rw [Real.log_mul two_ne_zero h2n, Real.log_mul two_ne_zero hnR.ne'] at hs2
  rw [Real.log_mul two_ne_zero hnR.ne'] at hs1
  norm_num at hs1 hs2 ⊢
  linarith

private theorem tendsto_double_nat : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
  tendsto_atTop_mono (fun n => by change n ≤ 2 * n; omega) tendsto_id

/-- The log-growth limit of `newprove`, using the Stirling limit
(s_n 	o sqrt{pi}) and the central binomial factorial formula. -/
theorem diagonal_log_growth (hStirling : Tendsto stirlingRatio atTop (𝓝 (Real.sqrt Real.pi))) :
    Tendsto (fun n : ℕ => Real.log (word n n).length / (2 * (n : ℝ))) atTop (𝓝 (Real.log 2)) := by
  have hs : Tendsto (fun n : ℕ => Real.log (stirlingRatio n)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (Real.sqrt_pos.2 Real.pi_pos).ne').tendsto.comp
      hStirling
  have hs2 := hs.comp tendsto_double_nat
  have hpart : Tendsto (fun n : ℕ =>
      (Real.log (stirlingRatio (2 * n)) - 2 * Real.log (stirlingRatio n)) / (n : ℝ))
      atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact (hs2.sub (hs.const_mul 2)).div_atTop hn
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlim := ((hpart.div_const 2).sub (hlog.div_const 4)).const_add (Real.log 2)
  simp only [zero_div, sub_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn'.ne'
  rw [log_diagonal_stirling n hn']
  field_simp [hnR]
  ring

/-- The ratio between the diagonal word length and (4^n/\sqrt{πn}). -/
noncomputable def centralScaled (n : Nat) : ℝ :=
  (word n n).length * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n

private theorem log_central_scaled (n : Nat) (hn : 0 < n) :
    Real.log (centralScaled n) = Real.log (stirlingRatio (2 * n)) -
      2 * Real.log (stirlingRatio n) + Real.log Real.pi / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlengthR : (0 : ℝ) < (word n n).length := by
    rw [length_diagonal_factorial n hn]
    positivity
  have hr : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
    norm_num
  rw [centralScaled, Real.log_div (mul_ne_zero hlengthR.ne' (Real.sqrt_pos.2 hr).ne')
    (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)), Real.log_mul hlengthR.ne'
    (Real.sqrt_pos.2 hr).ne', Real.log_sqrt hr.le, Real.log_mul Real.pi_pos.ne' hnR.ne',
    Real.log_pow, h4, log_diagonal_stirling n hn]
  ring

/-- The central-binomial asymptotic in the proof of `newprove`.
The premise is Stirling's theorem in its usual normalized form. -/
theorem central_binomial_stirling
    (hStirling : Tendsto stirlingRatio atTop (𝓝 (Real.sqrt Real.pi))) :
    Tendsto centralScaled atTop (𝓝 1) := by
  have hs : Tendsto (fun n : ℕ => Real.log (stirlingRatio n)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (Real.sqrt_pos.2 Real.pi_pos).ne').tendsto.comp hStirling
  have h := ((hs.comp tendsto_double_nat).sub (hs.const_mul 2)).add_const (Real.log Real.pi / 2)
  have he : Real.log (Real.sqrt Real.pi) - 2 * Real.log (Real.sqrt Real.pi) +
      Real.log Real.pi / 2 = 0 := by
    rw [Real.log_sqrt Real.pi_pos.le]
    ring
  rw [he] at h
  have hlog : Tendsto (fun n => Real.log (centralScaled n)) atTop (𝓝 0) := by
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (log_central_scaled n (by omega)).symm
  have hExp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  rw [Real.exp_zero] at hExp
  refine hExp.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply Real.exp_log
  unfold centralScaled
  rw [length_diagonal_factorial n (by omega)]
  positivity

/-- The classical Stirling limit cited in the proof of `newprove`. -/
private theorem stirlingRatio_tendsto :
    Tendsto stirlingRatio atTop (𝓝 (Real.sqrt Real.pi)) :=
  Stirling.tendsto_stirlingSeq_sqrt_pi

/-- The central binomial asymptotic in `newprove`, with Stirling's theorem
supplied by mathlib. -/
theorem central_binomial_asymptotic : Tendsto centralScaled atTop (𝓝 1) :=
  central_binomial_stirling stirlingRatio_tendsto

/-- The diagonal logarithmic growth claimed in `newprove`. -/
theorem diagonal_log_growth_stirling :
    Tendsto (fun n : ℕ => Real.log (word n n).length / (2 * (n : ℝ))) atTop (𝓝 (Real.log 2)) :=
  diagonal_log_growth stirlingRatio_tendsto

/-- The finite part of newprove in the source's binomial-coefficient
and real-density notation, with both indices starting at one. -/
theorem binomial_counts_and_densities {u v : Nat} (hu : 0 < u) (hv : 0 < v) :
    (word u v).length = (u + v).choose u ∧
      (word u v).count .a = (u + v - 1).choose u ∧
      (word u v).count .b = (u + v - 1).choose v ∧
      ((word u v).count .a : ℝ) / (word u v).length = (v : ℝ) / (u + v) ∧
      ((word u v).count .b : ℝ) / (word u v).length = (u : ℝ) / (u + v) := by
  have hlen : (word u v).length = (u + v).choose u := by
    rw [length_word u v (by omega), choose_eq_natChoose]
  have ha : (word u v).count .a = (u + v - 1).choose u := by
    obtain ⟨v', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv.ne'
    rw [count_a, choose_eq_natChoose, show u + (v' + 1) - 1 = u + v' by omega]
  have hb : (word u v).count .b = (u + v - 1).choose v := by
    obtain ⟨u', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu.ne'
    rw [count_b, choose_eq_natChoose, show u' + 1 + v - 1 = u' + v by omega]
  have hpos : 0 < (word u v).length := hlen ▸ Nat.choose_pos (Nat.le_add_right _ _)
  have hlenR : (0 : ℝ) < (word u v).length := by exact_mod_cast hpos
  have huv : (0 : ℝ) < (u : ℝ) + v := by positivity
  refine ⟨hlen, ha, hb, (div_eq_div_iff hlenR.ne' huv.ne').2 ?_,
    (div_eq_div_iff hlenR.ne' huv.ne').2 ?_⟩
  · exact_mod_cast (densities u v).1
  · exact_mod_cast (densities u v).2

end Thesis.LatticeWord
