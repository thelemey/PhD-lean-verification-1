import Thesis.SturmianPrefixRatios
import Thesis.SturmianDensityMeasure
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open Set Filter Metric MeasureTheory GenContFract
open scoped Topology ENNReal

namespace Thesis.SturmianDensity

/-- A fixed positive lower bound for the scaled approximation error. -/
def badApproximationCore (c : ℝ) : Set ℝ :=
  ⋂ (p : ℤ) (q : ℕ) (_ : 0 < q),
    {x | c / (q : ℝ) ^ 2 ≤ |x - (p : ℝ) / q|}

theorem mem_badApproximationCore {c x : ℝ} :
    x ∈ badApproximationCore c ↔
      ∀ (p : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ 2 ≤ |x - (p : ℝ) / q| := by
  simp only [badApproximationCore, mem_iInter, mem_setOf_eq]

theorem isClosed_badApproximationCore (c : ℝ) : IsClosed (badApproximationCore c) := by
  unfold badApproximationCore
  exact isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_id.sub continuous_const).abs

private theorem irrational_of_mem_core {c x : ℝ} (hc : 0 < c) (hx : x ∈ badApproximationCore c) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  have h := mem_badApproximationCore.1 hx r.num r.den r.pos
  rw [Rat.cast_def, sub_self, abs_zero] at h
  have hpos : 0 < c / (r.den : ℝ) ^ 2 := div_pos hc (pow_pos (by exact_mod_cast r.pos) 2)
  exact (not_le_of_gt hpos) h

private theorem exists_approximation_sequence {x : ℝ} (hx : Irrational x) :
    ∃ (p : ℕ → ℤ) (q : ℕ → ℕ), (∀ n, 0 < q n) ∧ Tendsto q atTop atTop ∧
      ∀ n, |x - (p n : ℝ) / q n| ≤ 1 / (q n : ℝ) ^ 2 := by
  let g := GenContFract.of x
  let s := (slopeFractions x hx).prefixBlocks
  let q := s.Q
  let p := fun n : ℕ => ⌊(g.contsAux (n + 2)).a⌋
  refine ⟨p, q, s.positive, s.increasing.tendsto_atTop, fun n => ?_⟩
  have hterm : ¬g.TerminatedAt (n + 1) := by
    intro h
    obtain ⟨r, hr⟩ := (GenContFract.terminates_iff_rat x).1 ⟨n + 1, h⟩
    exact hx ⟨r, hr.symm⟩
  have hd (n : ℕ) : (q n : ℝ) = g.dens (n + 1) := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
    exact continuedDenominator_eq_contsAux hx (n + 2)
  have hp : (p n : ℝ) = g.nums (n + 1) := by
    rw [num_eq_conts_a, nth_cont_eq_succ_nth_contAux]
    exact slope_contsAux_numerator_integer hx _
  have hb := GenContFract.abs_sub_convs_le hterm
  rw [conv_eq_num_div_den, ← hp, ← hd n] at hb
  have hden : g.dens (n + 1 + 1) = (q (n + 1) : ℝ) := (hd _).symm
  rw [hden] at hb
  have hQ : 0 < (q n : ℝ) := by exact_mod_cast s.positive n
  have hstep : (q n : ℝ) ≤ q (n + 1) := by exact_mod_cast s.increasing.monotone (Nat.le_succ n)
  apply hb.trans
  apply one_div_le_one_div_of_le (pow_pos hQ 2)
  rw [pow_two]
  exact mul_le_mul_of_nonneg_left hstep hQ.le

/-- The fixed-constant sets have measure zero. Around every point, close
rational approximations give excluded balls at arbitrarily small scales.
The moving-center form of the Lebesgue density theorem rules out density one. -/
theorem volume_badApproximationCore_zero {c : ℝ} (hc : 0 < c) :
    volume (badApproximationCore c) = 0 := by
  let S := badApproximationCore c
  let μ := (volume : Measure ℝ)
  have hS : MeasurableSet S := (isClosed_badApproximationCore c).measurableSet
  have hae : ∀ᵐ x ∂μ.restrict S, False := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ S (2 / c),
      ae_restrict_mem hS] with x hd hx
    obtain ⟨p, q, hq, hqtop, happ⟩ := exists_approximation_sequence (irrational_of_mem_core hc hx)
    let center := fun n => (p n : ℝ) / q n
    let r := fun n => c / (2 * (q n : ℝ) ^ 2)
    have hqR (n : ℕ) : 0 < (q n : ℝ) := by exact_mod_cast hq n
    have hr (n : ℕ) : 0 < r n := by
      dsimp only [r]
      exact div_pos hc (mul_pos (by norm_num) (pow_pos (hqR n) 2))
    have hlim : Tendsto r atTop (𝓝[>] 0) := by
      have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
      have hz := (tendsto_inv_atTop_zero.comp (hpow.comp hqtop)).const_mul (c / 2)
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hr⟩
      convert hz using 1
      · funext n
        change c / (2 * (q n : ℝ) ^ 2) = (c / 2) * ((q n : ℝ) ^ 2)⁻¹
        rw [← div_div, div_eq_mul_inv (c / 2)]
      · simp
    have hnear : ∀ᶠ n in atTop, x ∈ closedBall (center n) ((2 / c) * r n) := by
      filter_upwards [] with n
      rw [mem_closedBall, Real.dist_eq]
      have he : (2 / c) * r n = 1 / (q n : ℝ) ^ 2 := by
        dsimp [r]
        field_simp [hc.ne', (hqR n).ne']
      rw [he]
      exact happ n
    have hrate := hd center r hlim hnear
    have hhole (n : ℕ) : S ∩ closedBall (center n) (r n) = ∅ := by
      apply eq_empty_iff_forall_not_mem.2
      intro y hy
      have hlo := mem_badApproximationCore.1 hy.1 (p n) (q n) (hq n)
      have hhi : |y - center n| ≤ r n := by simpa only [mem_closedBall, Real.dist_eq] using hy.2
      have hlt : r n < c / (q n : ℝ) ^ 2 := by
        dsimp [r]
        apply div_lt_div_of_pos_left hc (pow_pos (hqR n) 2)
        nlinarith [pow_pos (hqR n) 2]
      exact (not_le_of_gt (hhi.trans_lt hlt)) hlo
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 1) := by
      simpa only [hhole, measure_empty, ENNReal.zero_div] using hrate
    exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hzero)
  have hz := ae_iff.1 hae
  simpa [μ, Measure.restrict_apply, S] using hz

/-- The nullity result used in the thesis as a consequence of Khinchin. -/
theorem volume_badlyApproximableSlopes_zero : volume badlyApproximableSlopes = 0 := by
  have hs : badlyApproximableSlopes ⊆ ⋃ n : ℕ, badApproximationCore (1 / ((n : ℝ) + 1)) := by
    rintro x ⟨_, c, hc, h⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / c)
    have hsmall : 1 / ((n : ℝ) + 1) ≤ c := by
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
      have ht := (div_lt_iff₀ hc).1 hn
      nlinarith
    refine mem_iUnion.2 ⟨n, mem_badApproximationCore.2 fun p q hq => ?_⟩
    exact (div_le_div_of_nonneg_right hsmall (by positivity)).trans (h p q hq)
  exact measure_mono_null hs
    (measure_iUnion_null fun n => volume_badApproximationCore_zero (by positivity))

end Thesis.SturmianDensity
