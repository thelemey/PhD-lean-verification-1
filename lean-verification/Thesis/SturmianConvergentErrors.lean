import Thesis.SturmianPrefixRatios

open GenContFract

namespace Thesis.SturmianDensity

private theorem continuedFraction_stream_succ_some {a : ℝ} (ha : Irrational a) (k : Nat) :
    ∃ p, IntFractPair.stream a (k + 1) = some p := by
  apply Option.ne_none_iff_exists'.1
  intro hn
  have hterm := (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2 hn
  obtain ⟨q, hq⟩ := (GenContFract.terminates_iff_rat a).1 ⟨k, hterm⟩
  exact ha ⟨q, hq.symm⟩

private theorem continuedFraction_stream_some {a : ℝ} (ha : Irrational a) (k : Nat) :
    ∃ p, IntFractPair.stream a k = some p := by
  cases k with
  | zero => exact ⟨IntFractPair.of a, rfl⟩
  | succ k => exact continuedFraction_stream_succ_some ha k

private theorem aux_num_step {a : ℝ} (ha : Irrational a) (k : Nat) :
    ((GenContFract.of a).contsAux (k + 2)).a =
      (partialQuotient a k : ℝ) * ((GenContFract.of a).contsAux (k + 1)).a +
        ((GenContFract.of a).contsAux k).a := by
  obtain ⟨p, hp⟩ := continuedFraction_stream_succ_some ha k
  have hg := get?_of_eq_some_of_succ_get?_intFractPair_stream hp
  have h := GenContFract.contsAux_recurrence hg rfl rfl
  have hp_pos := IntFractPair.one_le_succ_nth_stream_b hp
  have hcast : (p.b : ℝ) = (partialQuotient a k : ℝ) := by
    have hc : ((partialQuotient a k : Nat) : ℤ) = p.b := by
      simp [partialQuotient, hp, Int.toNat_of_nonneg (zero_le_one.trans hp_pos)]
    exact_mod_cast hc.symm
  simpa [nextConts, nextNum, hcast, add_comm] using congrArg GenContFract.Pair.a h

/-- The signed integer-approximation error q_k α - p_k. -/
noncomputable def convergentError (a : ℝ) (k : Nat) : ℝ :=
  ((GenContFract.of a).contsAux (k + 1)).b * a -
    ((GenContFract.of a).contsAux (k + 1)).a

/-- The alternating orientation makes each error magnitude positive. -/
noncomputable def convergentErrorMagnitude (a : ℝ) (k : Nat) : ℝ :=
  (-1 : ℝ) ^ k * convergentError a k

theorem convergentErrorMagnitude_pos {a : ℝ} (ha : Irrational a) (k : Nat) :
    0 < convergentErrorMagnitude a k := by
  obtain ⟨p, hp⟩ := continuedFraction_stream_some ha k
  obtain ⟨pn, hpn⟩ := continuedFraction_stream_succ_some ha k
  have hpne : p.fr ≠ 0 := by
    intro hzero
    have hn : IntFractPair.stream a (k + 1) = none := by
      rw [IntFractPair.stream, hp]
      simp [hzero]
    rw [hpn] at hn
    contradiction
  have hpr : 0 < p.fr :=
    lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg hp) hpne.symm
  let g := GenContFract.of a
  let Q := (g.contsAux (k + 1)).b
  let P := (g.contsAux (k + 1)).a
  let Q₀ := (g.contsAux k).b
  have hQ : 0 < Q := by
    change 0 < ((GenContFract.of a).contsAux (k + 1)).b
    rw [← continuedDenominator_eq_contsAux ha]
    exact_mod_cast continuedDenominator_pos (slopeFractions a ha) k
  have hQ₀ : 0 ≤ Q₀ := by
    change 0 ≤ ((GenContFract.of a).contsAux k).b
    rw [← continuedDenominator_eq_contsAux ha]
    positivity
  have hd : 0 < p.fr⁻¹ * Q + Q₀ :=
    add_pos_of_pos_of_nonneg (mul_pos (inv_pos.2 hpr) hQ) hQ₀
  have hg : g.convs k = P / Q := by
    rw [conv_eq_num_div_den, num_eq_conts_a, den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have he := GenContFract.sub_convs_eq hp
  simp only [hpne, if_false] at he
  change a - g.convs k = (-1 : ℝ) ^ k / (Q * (p.fr⁻¹ * Q + Q₀)) at he
  rw [hg] at he
  have herr : convergentError a k = (-1 : ℝ) ^ k / (p.fr⁻¹ * Q + Q₀) := by
    change Q * a - P = _
    calc
      _ = Q * (a - P / Q) := by field_simp [hQ.ne']; ring
      _ = _ := by rw [he, ← div_div, ← mul_div_assoc, mul_div_cancel₀ _ hQ.ne']
  rw [convergentErrorMagnitude, herr, ← mul_div_assoc, ← mul_pow]
  norm_num
  exact hd

theorem convergentError_step (a : ℝ) (ha : Irrational a) (k : Nat) :
    convergentError a (k + 2) =
      (partialQuotient a (k + 1) : ℝ) * convergentError a (k + 1) + convergentError a k := by
  unfold convergentError
  have hd := slope_contsAux_den_step ha (k + 1)
  have hn := aux_num_step ha (k + 1)
  have hidx : k + 2 + 1 = k + 1 + 2 := by omega
  rw [hidx, hd, hn]
  ring

/-- The absolute errors obey the subtractive Euclidean recurrence
underlying the blocks of intermediate convergents. -/
theorem convergentErrorMagnitude_step {a : ℝ} (ha : Irrational a) (k : Nat) :
    convergentErrorMagnitude a k =
      (partialQuotient a (k + 1) : ℝ) * convergentErrorMagnitude a (k + 1) +
        convergentErrorMagnitude a (k + 2) := by
  simp only [convergentErrorMagnitude, convergentError_step a ha k, pow_succ]
  ring

/-- The first two absolute errors for a slope between zero and one. -/
theorem initial_convergentErrorMagnitudes {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hirr : Irrational a) :
    convergentErrorMagnitude a 0 = a ∧
      convergentErrorMagnitude a 1 = 1 - (partialQuotient a 0 : ℝ) * a := by
  have hf : ⌊a⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨ha.le, ha'⟩
  have hhead : (GenContFract.of a).h = 0 := of_h_eq_floor.trans (by simp [hf])
  have hn := aux_num_step hirr 0
  have hd := slope_contsAux_den_step hirr 0
  change ((GenContFract.of a).contsAux 2).a =
    (partialQuotient a 0 : ℝ) * (GenContFract.of a).h + 1 at hn
  rw [hhead, mul_zero, zero_add] at hn
  change ((GenContFract.of a).contsAux 2).b = (partialQuotient a 0 : ℝ) * 1 + 0 at hd
  rw [mul_one, add_zero] at hd
  constructor
  · change (-1 : ℝ) ^ 0 * (1 * a - (GenContFract.of a).h) = a
    rw [hhead, sub_zero, pow_zero, one_mul, one_mul]
  · have heN : ((GenContFract.of a).contsAux 2).a = 1 := hn
    have heD : ((GenContFract.of a).contsAux 2).b = (partialQuotient a 0 : ℝ) := hd
    simp only [convergentErrorMagnitude, convergentError, Nat.reduceAdd, pow_one, heN, heD]
    ring

end Thesis.SturmianDensity
