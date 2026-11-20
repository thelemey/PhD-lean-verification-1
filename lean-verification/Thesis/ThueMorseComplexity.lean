import Thesis.ThueMorseRecurrence
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology

namespace Thesis.ThueMorse

variable {A : Type*} [Fintype A]

/-- The finite language at a prescribed length. -/
noncomputable def factorLanguage (w : Nat → A) (k : Nat) : Finset (Fin k → A) := by
  classical
  exact Finset.univ.filter fun u => ∃ i, window w k i = u

@[simp]
theorem mem_factorLanguage (w : Nat → A) (k : Nat) (u : Fin k → A) :
    u ∈ factorLanguage w k ↔ ∃ i, window w k i = u := by
  simp [factorLanguage]

noncomputable def complexity (w : Nat → A) (k : Nat) : Nat :=
  (factorLanguage w k).card

theorem factorLanguage_prefix_image [DecidableEq A] (w : Nat → A) (k : Nat) :
    (factorLanguage w (k + 1)).image (fun f j => f (Fin.castSucc j)) =
      factorLanguage w k := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨v, hv, huv⟩ := Finset.mem_image.mp hu
    obtain ⟨i, rfl⟩ := (mem_factorLanguage _ _ _).1 hv
    exact (mem_factorLanguage _ _ _).2 ⟨i, huv⟩
  · intro hu
    obtain ⟨i, rfl⟩ := (mem_factorLanguage _ _ _).1 hu
    exact Finset.mem_image.mpr ⟨window w (k+1) i, (mem_factorLanguage _ _ _).2 ⟨i, rfl⟩, rfl⟩

private theorem periodic_of_complexity_eq (w : Nat → A) (k : Nat)
    (he : complexity w k = complexity w (k + 1)) :
    ∃ i m : Nat, 0 < m ∧ ∀ t, w (i + t + m) = w (i + t) := by
  classical
  let prefixMap : (Fin (k + 1) → A) → (Fin k → A) := fun f j => f (Fin.castSucc j)
  have hinj : Set.InjOn prefixMap (factorLanguage w (k + 1) : Set (Fin (k + 1) → A)) := by
    apply Finset.card_image_iff.1
    rw [factorLanguage_prefix_image]
    exact he
  have hextend (i j : Nat) (hij : window w k i = window w k j) :
      window w (k + 1) i = window w (k + 1) j :=
    hinj ((mem_factorLanguage _ _ _).2 ⟨i, rfl⟩)
      ((mem_factorLanguage _ _ _).2 ⟨j, rfl⟩) hij
  obtain ⟨i, _, j, _, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (complexity w k + 1)) (t := factorLanguage w k)
    (f := window w k) (by simp [complexity]) (fun i _ => (mem_factorLanguage _ _ _).2 ⟨i, rfl⟩)
  suffices h : ∀ a c : Nat, a < c → window w k a = window w k c →
      ∃ i m : Nat, 0 < m ∧ ∀ t, w (i + t + m) = w (i + t) by
    rcases lt_or_gt_of_ne hij with hh | hh
    · exact h i j hh heq
    · exact h j i hh heq.symm
  intro a c hac hacwin
  have hsame (t : Nat) : window w k (a + t) = window w k (c + t) := by
    induction t with
    | zero => simpa using hacwin
    | succ t ih =>
      funext l
      simpa only [window, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1 (l : Nat)] using
        congrFun (hextend (a + t) (c + t) ih) l.succ
  refine ⟨a, c - a, by omega, fun t => ?_⟩
  let first : Fin (k + 1) := ⟨0, Nat.zero_lt_succ _⟩
  have hletter := congrFun (hextend (a + t) (c + t) (hsame t)) first
  have hx : a + t + (c - a) = c + t := by omega
  rw [hx]
  simpa [first, window] using hletter.symm

/-- The Morse–Hedlund lower bound in the form used in thm:dynWb. -/
theorem complexity_ge_of_not_eventually_periodic (w : Nat → A)
    (h : ¬ ∃ i m : Nat, 0 < m ∧ ∀ t, w (i + t + m) = w (i + t)) (k : Nat) :
    k + 1 ≤ complexity w k := by
  classical
  induction k with
  | zero =>
    have hn : (factorLanguage w 0).Nonempty := ⟨window w 0 0,
      (mem_factorLanguage _ _ _).2 ⟨0, rfl⟩⟩
    exact Finset.card_pos.mpr hn
  | succ k ih =>

    have hcard : complexity w k ≤ complexity w (k + 1) := by
      unfold complexity
      rw [← factorLanguage_prefix_image w k]
      exact Finset.card_image_le
    have hne : complexity w k ≠ complexity w (k + 1) :=
      fun he => h (periodic_of_complexity_eq w k he)
    omega

private def blockCode (b N e k : Nat) (hN : 0 < N)
    (c : Fin N × Fin N × Fin (b ^ e)) : Fin k → Fin N := fun f =>
  ⟨twoBlockLetter b N e c.1 c.2.1 (c.2.2 + f), by
    unfold twoBlockLetter
    split_ifs <;> exact Nat.mod_lt _ hN⟩

/-- Every occurrence is encoded by the two desubstituted letters and
an offset, proving the upper bound in thm:dynWb (3). -/
theorem complexity_upper {b N k : Nat} (hb : 1 < b) (hN : 0 < N) (hk : 0 < k) :
    complexity (finiteWord b N hN) k < N ^ 2 * b * k := by
  classical
  obtain ⟨e, he, he'⟩ := exists_covering_power hb hk
  let B := b ^ e
  let code := blockCode b N e k hN
  have hsub : factorLanguage (finiteWord b N hN) k ⊆ Finset.univ.image code := by
    intro u hu
    obtain ⟨i, rfl⟩ := (mem_factorLanguage _ _ _).1 hu
    let m := i / B
    have hB : 0 < B := Nat.pow_pos (by omega)
    have hr : i % B < B := Nat.mod_lt i hB
    let r : Fin B := ⟨i % B, hr⟩
    refine Finset.mem_image.2 ⟨(finiteWord b N hN m, finiteWord b N hN (m + 1), r),
      Finset.mem_univ _, ?_⟩
    funext l
    apply Fin.ext
    have hl : (l : Nat) < k := l.isLt
    have ht : i % B + l < 2 * B := by change k ≤ B at he; omega
    have hde : B * m + i % B = i := by rw [Nat.add_comm, Nat.mod_add_div]
    have h := word_in_two_blocks (N := N) hb e m (i % B + l) ht
    rw [← Nat.add_assoc, hde] at h
    exact h.symm
  have hc : complexity (finiteWord b N hN) k ≤ N ^ 2 * B := by
    unfold complexity
    apply (Finset.card_le_card hsub).trans
    apply Finset.card_image_le.trans
    simp [code, B, Fintype.card_prod, pow_two, Nat.mul_assoc]
  exact hc.trans_lt (by
    rw [Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_left he' (Nat.pow_pos hN))

/-- Both complexity bounds for the non-eventually-periodic word. -/
theorem complexity_bounds {b N k : Nat} (hb : 1 < b) (hN : 0 < N) (hk : 0 < k)
    (ha : ¬ N ∣ b - 1) :
    k + 1 ≤ complexity (finiteWord b N hN) k ∧
      complexity (finiteWord b N hN) k < N ^ 2 * b * k := by
  refine ⟨complexity_ge_of_not_eventually_periodic _ ?_ k, complexity_upper hb hN hk⟩
  rintro ⟨i, m, hm, hp⟩
  exact not_eventually_periodic_word hb hN ha ⟨i, m, hm, fun t => congrArg Fin.val (hp t)⟩

/-- The entropy expression of a finite-alphabet subshift, evaluated on
the language of the digit-sum word. -/
theorem complexity_entropy_rate_zero {b N : Nat} (hb : 1 < b) (hN : 0 < N)
    (ha : ¬ N ∣ b - 1) :
    Tendsto (fun k : Nat => Real.log (complexity (finiteWord b N hN) k : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
  let C : ℝ := (N ^ 2 * b : Nat)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc := (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).add hlog
  rw [zero_add] at hc
  refine squeeze_zero' ?_ ?_ hc
  · filter_upwards [eventually_gt_atTop (0 : Nat)] with k hk
    have h := (complexity_bounds hb hN hk ha).1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ complexity (finiteWord b N hN) k by omega))) (by positivity)
  · filter_upwards [eventually_gt_atTop (0 : Nat)] with k hk
    have hpos : 0 < (complexity (finiteWord b N hN) k : ℝ) := by
      have h := (complexity_bounds hb hN hk ha).1
      exact_mod_cast (show 0 < complexity (finiteWord b N hN) k by omega)
    have hle : (complexity (finiteWord b N hN) k : ℝ) ≤ C * k := by
      dsimp [C]
      exact_mod_cast (complexity_upper hb hN hk).le
    simp only [Function.comp_apply, id_eq] at *
    rw [← add_div, ← Real.log_mul hC.ne' (by positivity : (k : ℝ) ≠ 0)]
    exact div_le_div_of_nonneg_right (Real.log_le_log hpos hle) (by positivity)

end Thesis.ThueMorse
