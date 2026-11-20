import Thesis.SturmianDensityDichotomy
import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

open GenContFract
open scoped Rat

namespace Thesis.SturmianDensity

private theorem not_terminated_at {a : ℝ} (ha : Irrational a) (n : Nat) :
    ¬ (GenContFract.of a).TerminatedAt n := by
  intro hn
  obtain ⟨q, hq⟩ := (GenContFract.terminates_iff_rat a).mp ⟨n, hn⟩
  exact ha ⟨q, hq.symm⟩

private theorem stream_succ_some {a : ℝ} (ha : Irrational a) (n : Nat) :
    ∃ s, IntFractPair.stream a (n + 1) = some s := by
  obtain ⟨gp, hg⟩ := Option.ne_none_iff_exists'.mp (not_terminated_at ha n)
  obtain ⟨s, hs, _⟩ := IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hg
  exact ⟨s, hs⟩

/-- The positive partial quotients of the simple continued fraction of
an irrational real, indexed from zero after the integer part. -/
noncomputable def partialQuotient (a : ℝ) (n : Nat) : Nat :=
  ((IntFractPair.stream a (n + 1)).map (fun s => s.b.toNat)).getD 0

private theorem partialQuotient_eq {a : ℝ} {n : Nat} {s : IntFractPair ℝ}
    (hs : IntFractPair.stream a (n + 1) = some s) :
    ((partialQuotient a n : Nat) : ℤ) = s.b := by
  have h := IntFractPair.one_le_succ_nth_stream_b hs
  simp [partialQuotient, hs, Int.toNat_of_nonneg (zero_le_one.trans h)]

theorem partialQuotient_pos {a : ℝ} (ha : Irrational a) (n : Nat) :
    0 < partialQuotient a n := by
  obtain ⟨s, hs⟩ := stream_succ_some ha n
  have h := IntFractPair.one_le_succ_nth_stream_b hs
  rw [← partialQuotient_eq hs] at h
  exact_mod_cast h

/-- The reversed finite fractions attached to the partial quotients
of the irrational slope via the recurrence used in the source. -/
noncomputable def slopeFractions (a : ℝ) (ha : Irrational a) : ReversedFractions :=
  ReversedFractions.ofQuotients (partialQuotient a) (partialQuotient_pos ha)

private theorem partDen_eq {a : ℝ} (ha : Irrational a) (n : Nat) :
    (GenContFract.of a).partDens.get? n = some (partialQuotient a n : ℝ) := by
  obtain ⟨s, hs⟩ := stream_succ_some ha n
  have h := partDen_eq_s_b (get?_of_eq_some_of_succ_get?_intFractPair_stream hs)
  have he : (s.b : ℝ) = (partialQuotient a n : ℝ) := by
    exact_mod_cast (partialQuotient_eq hs).symm
  simpa only [he] using h

/-- The denominator recurrence with the actual simple continued
fraction quotients of the slope. -/
theorem slope_contsAux_den_step {a : ℝ} (ha : Irrational a) (n : Nat) :
    ((GenContFract.of a).contsAux (n + 2)).b =
      (partialQuotient a n : ℝ) * ((GenContFract.of a).contsAux (n + 1)).b +
        ((GenContFract.of a).contsAux n).b := by
  obtain ⟨s, hs⟩ := stream_succ_some ha n
  have hg := get?_of_eq_some_of_succ_get?_intFractPair_stream hs
  have h := GenContFract.contsAux_recurrence hg rfl rfl
  have hsB : (s.b : ℝ) = (partialQuotient a n : ℝ) := by
    exact_mod_cast (partialQuotient_eq hs).symm
  simpa [nextConts, nextDen, hsB, add_comm] using congrArg GenContFract.Pair.b h

private theorem conts_integer {a : ℝ} (ha : Irrational a) (n : Nat) :
    ∃ u v : ℤ, (GenContFract.of a).contsAux n = ⟨(u : ℝ), (v : ℝ)⟩ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · exact ⟨1, 0, by simp [GenContFract.contsAux]⟩
    · exact ⟨⌊a⌋, 1, by simp [GenContFract.contsAux]⟩
    · obtain ⟨u, v, huv⟩ := ih n (by omega)
      obtain ⟨U, V, hUV⟩ := ih (n + 1) (by omega)
      obtain ⟨s, hs⟩ := stream_succ_some ha n
      have hg := get?_of_eq_some_of_succ_get?_intFractPair_stream hs
      refine ⟨u + s.b * U, v + s.b * V, ?_⟩
      rw [GenContFract.contsAux_recurrence hg huv hUV]
      simp [nextConts, nextNum, nextDen, add_comm]

private theorem exists_rat_convergent_den {a : ℝ} (ha : Irrational a) (n : Nat) :
    ∃ q : ℚ, (q : ℝ) = (GenContFract.of a).convs n ∧
      (q.den : ℝ) = (GenContFract.of a).dens n := by
  obtain ⟨u, v, huv⟩ := conts_integer ha (n + 1)
  obtain ⟨U, V, hUV⟩ := conts_integer ha n
  have hd := (SimpContFract.of a).determinant_aux (n := n)
    (Or.inr (not_terminated_at ha (n - 1)))
  change ((GenContFract.of a).contsAux n).a * ((GenContFract.of a).contsAux (n + 1)).b -
    ((GenContFract.of a).contsAux n).b * ((GenContFract.of a).contsAux (n + 1)).a = (-1) ^ n at hd
  rw [huv, hUV] at hd
  change (U : ℝ) * v - (V : ℝ) * u = (-1 : ℝ) ^ n at hd
  have hdZ : U * v - V * u = (-1 : ℤ) ^ n := by exact_mod_cast hd
  have hB := succ_nth_fib_le_of_nth_den (v := a) (n := n) (Or.inr (not_terminated_at ha (n - 1)))
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, huv] at hB
  have hfib : (0 : ℝ) < (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast (Nat.fib_pos.2 (Nat.succ_pos n))
  have hvR : (0 : ℝ) < v := hfib.trans_le hB
  have hv : 0 < v := by exact_mod_cast hvR
  have hvn : ((v.toNat : Nat) : ℤ) = v := Int.toNat_of_nonneg hv.le
  have hcop : IsCoprime u v := by
    let e : ℤ := (-1) ^ n
    refine ⟨-e * V, e * U, ?_⟩
    have he : e * e = 1 := by dsimp [e]; rw [← mul_pow]; norm_num
    calc
      _ = e * (U * v - V * u) := by ring
      _ = 1 := by rw [hdZ]; exact he
  have hcop' : u.natAbs.Coprime v.toNat := by
    have habs := congrArg Int.natAbs hvn
    rw [Int.natAbs_natCast] at habs
    rw [habs]
    exact Int.isCoprime_iff_nat_coprime.mp hcop
  let q : ℚ := ⟨u, v.toNat, by omega, hcop'⟩
  have hden : (v.toNat : ℝ) = (v : ℝ) := by exact_mod_cast hvn
  refine ⟨q, ?_, ?_⟩
  · rw [conv_eq_num_div_den, num_eq_conts_a, den_eq_conts_b,
      nth_cont_eq_succ_nth_contAux, huv, Rat.cast_def]
    change (u : ℝ) / (v.toNat : ℝ) = (u : ℝ) / (v : ℝ)
    rw [hden]
  · rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, huv]
    exact hden

private theorem den_pos {a : ℝ} (ha : Irrational a) (n : Nat) :
    0 < (GenContFract.of a).dens n := by
  obtain ⟨q, _, hq⟩ := exists_rat_convergent_den ha n
  rw [← hq]
  exact_mod_cast Nat.pos_of_ne_zero q.den_nz

/-- The reversed finite fraction is the ratio of consecutive
continuant denominators, with the initial pair (0, 1). -/
theorem slopeFractions_t_eq_continuant_ratio {a : ℝ} (ha : Irrational a) (n : Nat) :
    (slopeFractions a ha).t n =
      ((GenContFract.of a).contsAux n).b / ((GenContFract.of a).contsAux (n + 1)).b := by
  let g := GenContFract.of a
  let s := slopeFractions a ha
  change s.t n = (g.contsAux n).b / (g.contsAux (n + 1)).b
  induction n with
  | zero =>
    change 0 = (g.contsAux 0).b / (g.contsAux 1).b
    simp [GenContFract.contsAux]
  | succ n ih =>
    obtain ⟨digit, hstream⟩ := stream_succ_some ha n
    have hpart := get?_of_eq_some_of_succ_get?_intFractPair_stream hstream
    have hb : 0 < (g.contsAux (n + 1)).b := den_pos ha n
    have hprev : 0 ≤ (g.contsAux n).b := zero_le_of_contsAux_b
    have hdigit : (digit.b : ℝ) = (s.a n : ℝ) := by
      change (digit.b : ℝ) = (partialQuotient a n : ℝ)
      exact_mod_cast (partialQuotient_eq hstream).symm
    have hpos : (0 : ℝ) < s.a n := by exact_mod_cast s.a_pos n
    have hrec : (g.contsAux (n + 2)).b =
        (s.a n : ℝ) * (g.contsAux (n + 1)).b + (g.contsAux n).b := by
      rw [GenContFract.contsAux_recurrence hpart rfl rfl]
      simp [g, GenContFract.nextConts, GenContFract.nextDen, hdigit, add_comm]
    rw [s.step, ih, hrec]
    have hsum : (0 : ℝ) < (s.a n : ℝ) + (g.contsAux n).b / (g.contsAux (n + 1)).b :=
      add_pos_of_pos_of_nonneg hpos (div_nonneg hprev hb.le)
    have hden : 0 < (s.a n : ℝ) * (g.contsAux (n + 1)).b + (g.contsAux n).b :=
      add_pos_of_pos_of_nonneg (mul_pos hpos hb) hprev
    field_simp [hb.ne', hsum.ne', hden.ne']

private theorem convergent_lower_bound {a : ℝ} (ha : Irrational a) (n A : Nat)
    (hA : partialQuotient a n ≤ A) :
    1 / (((A : ℝ) + 2) * (GenContFract.of a).dens n ^ 2) ≤
      |a - (GenContFract.of a).convs n| := by
  obtain ⟨s, hs⟩ := stream_succ_some ha n
  obtain ⟨t, ht, htnz, he⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hs
  let g := GenContFract.of a
  let B := g.dens n
  let Bprev := (g.contsAux n).b
  have hB : 0 < B := den_pos ha n
  have hBprev : 0 ≤ Bprev := zero_le_of_contsAux_b
  have hprev : Bprev ≤ B := by
    cases n with
    | zero => simpa [Bprev, GenContFract.contsAux] using hB.le
    | succ n =>
      have h := of_den_mono (v := a) (n := n)
      change (g.contsAux (n + 1)).b ≤ g.dens (n + 1) at h
      exact h
  have hf : 0 < t.fr :=
    lt_of_le_of_ne' (IntFractPair.nth_stream_fr_nonneg ht) htnz
  have hfloor : t.fr⁻¹ < (s.b : ℝ) + 1 := by
    rw [← he]
    exact Int.lt_floor_add_one _
  have hcast : (s.b : ℝ) ≤ A := by
    rw [show (s.b : ℝ) = (partialQuotient a n : ℝ) by exact_mod_cast (partialQuotient_eq hs).symm]
    exact_mod_cast hA
  have hden : 0 < B * (t.fr⁻¹ * B + Bprev) := by positivity
  have herr := sub_convs_eq ht
  change a - g.convs n =
    if t.fr = 0 then 0 else (-1) ^ n / ((g.contsAux (n + 1)).b *
      (t.fr⁻¹ * (g.contsAux (n + 1)).b + (g.contsAux n).b)) at herr
  rw [if_neg htnz, ← nth_cont_eq_succ_nth_contAux, ← den_eq_conts_b] at herr
  change a - g.convs n = (-1) ^ n / (B * (t.fr⁻¹ * B + Bprev)) at herr
  change 1 / (((A : ℝ) + 2) * B ^ 2) ≤ |a - g.convs n|
  rw [herr, abs_div, abs_neg_one_pow, abs_of_pos hden]
  apply one_div_le_one_div_of_le hden
  calc
    B * (t.fr⁻¹ * B + Bprev) ≤ B * (((A : ℝ) + 1) * B + B) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right (by linarith) hB.le) hprev) hB.le
    _ = _ := by ring

private theorem badly_approx_of_rat_lower {a c : ℝ} (hc : 0 < c)
    (h : ∀ r : ℚ, c / (r.den : ℝ) ^ 2 ≤ |a - (r : ℝ)|) :
    BadlyApproximable a := by
  refine ⟨c, hc, ?_⟩
  intro p q hq
  let r := mkRat p q
  have he : (r : ℝ) = (p : ℝ) / q := by
    rw [show r = p /. (q : ℤ) by exact (Rat.divInt_ofNat p q).symm]
    exact Rat.cast_divInt_of_ne_zero p (by exact_mod_cast hq.ne')
  have hq' : r.den ≤ q := by
    have hnz := hq.ne'
    have hR := (Rat.normalize_num_den' p q hnz)
    obtain ⟨f, hf, _, hfq⟩ := hR
    rw [Rat.normalize_eq_mkRat] at hfq
    change q = r.den * f at hfq
    exact Nat.le_of_dvd hq ⟨f, hfq⟩
  have hqR : (r.den : ℝ) ≤ q := by exact_mod_cast hq'
  have hpR : 0 < (r.den : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero r.den_nz
  rw [← he]
  exact (div_le_div_of_nonneg_left hc.le (pow_pos hpR 2)
    (pow_le_pow_left₀ hpR.le hqR 2)).trans (h r)

/-- The classical criterion used at the end of `prop:dichotomy`.
For bounded quotients the exact convergent error and Legendre's theorem
give a uniform lower bound, and the convergent upper error gives the
converse. -/
theorem slopeFractions_bounded_iff_badlyApproximable {a : ℝ} (ha : Irrational a) :
    (slopeFractions a ha).BoundedQuotients ↔ BadlyApproximable a := by
  constructor
  · rintro ⟨A, hA⟩
    let c : ℝ := min (1 / 2) (1 / ((A : ℝ) + 2))
    have hc : 0 < c := lt_min (by norm_num) (by positivity)
    apply badly_approx_of_rat_lower hc
    intro r
    have hp : 0 < (r.den : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero r.den_nz
    by_cases hr : |a - (r : ℝ)| < 1 / (2 * (r.den : ℝ) ^ 2)
    · obtain ⟨n, hn⟩ := Real.exists_convs_eq_rat hr
      obtain ⟨q, hq, hd⟩ := exists_rat_convergent_den ha n
      have he : q = r := by exact_mod_cast (hq.trans hn)
      subst q
      have hb := convergent_lower_bound ha n A (hA n)
      rw [hn, ← hd] at hb
      exact (div_le_div_of_nonneg_right (min_le_right _ _) (pow_nonneg hp.le 2)).trans
        (by simpa only [div_div] using hb)
    · have h := div_le_div_of_nonneg_right (min_le_left (1 / 2 : ℝ) (1 / ((A : ℝ) + 2)))
        (pow_nonneg hp.le 2)
      exact h.trans (by simpa only [div_div] using le_of_not_gt hr)
  · rintro ⟨c, hc, h⟩
    refine ⟨⌈1 / c⌉₊, fun n => ?_⟩
    obtain ⟨q, hq, hd⟩ := exists_rat_convergent_den ha n
    have hr : c / (q.den : ℝ) ^ 2 ≤ |a - (q : ℝ)| := by
      simpa only [← Rat.cast_def] using h q.num q.den (Nat.pos_of_ne_zero q.den_nz)
    have hu := abs_sub_convergents_le' (partDen_eq ha n)
    rw [← hq, ← hd] at hu
    have hqR : 0 < (q.den : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero q.den_nz
    have hn : (0 : ℝ) < partialQuotient a n := by exact_mod_cast partialQuotient_pos ha n
    have hmul := (div_le_div_iff₀ (pow_pos hqR 2) (by positivity)).mp (hr.trans hu)
    have hcancel : c * (partialQuotient a n : ℝ) ≤ 1 := by
      apply (mul_le_mul_iff_of_pos_right (pow_pos hqR 2)).mp
      nlinarith only [hmul]
    have hbound : (partialQuotient a n : ℝ) ≤ 1 / c := (le_div_iff₀ hc).2 (by linarith)
    exact_mod_cast hbound.trans (Nat.le_ceil _)

/-- The diophantine form of the dichotomy for the continued fraction
of the irrational slope, with Fischler's density formula as stated in
the dissertation. -/
theorem slope_density_gt_half_iff {a : ℝ} (ha : Irrational a) :
    1 / 2 < (slopeFractions a ha).fischlerDensity ↔ BadlyApproximable a :=
  (density_gt_half_iff (slopeFractions a ha)).trans (slopeFractions_bounded_iff_badlyApproximable ha)

end Thesis.SturmianDensity
