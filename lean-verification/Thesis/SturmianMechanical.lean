import Thesis.FactorTreeSpecial
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.Linarith

open Thesis.ThueMorse (mem_factorLanguage window)

namespace Thesis.FactorTree

/-- The cumulative floor function of the lower mechanical word. -/
private noncomputable def mechanicalFloor (a t : ℝ) (j : Nat) : ℤ :=
  ⌊t + (j : ℝ) * a⌋

/-- A letter of the lower mechanical word of slope a and intercept t.
For 0 < a < 1 the two successive floors differ by either zero or one. -/
noncomputable def mechanicalLetter (a t : ℝ) (j : Nat) : Bool :=
  decide (mechanicalFloor a t (j + 1) = mechanicalFloor a t j + 1)

/-- The characteristic word uses its slope as its intercept, as in
deffSturmiann1. The letters 0 and 1 are represented by false and true. -/
noncomputable def characteristicWord (a : ℝ) : Nat → Bool :=
  mechanicalLetter a a

theorem characteristic_letter_floor_eq (a : ℝ) (i : Nat) :
    characteristicWord a i =
      decide (⌊((i : ℝ) + 2) * a⌋ = ⌊((i : ℝ) + 1) * a⌋ + 1) := by
  unfold characteristicWord mechanicalLetter mechanicalFloor
  push_cast
  congr 1
  congr 1 <;> ring_nf

private theorem floor_step (a t : ℝ) (j : Nat) (ha : 0 < a) (ha' : a < 1) :
    mechanicalFloor a t j ≤ mechanicalFloor a t (j + 1) ∧
      mechanicalFloor a t (j + 1) ≤ mechanicalFloor a t j + 1 := by
  unfold mechanicalFloor
  push_cast
  constructor
  · apply Int.floor_mono
    linarith
  · rw [Int.floor_le_iff]
    push_cast
    have := Int.lt_floor_add_one (t + (j : ℝ) * a)
    linarith

theorem mechanicalFloor_step_eq (a t : ℝ) (j : Nat) (ha : 0 < a) (ha' : a < 1) :
    mechanicalFloor a t (j + 1) =
      mechanicalFloor a t j + if mechanicalLetter a t j then 1 else 0 := by
  have h := floor_step a t j ha ha'
  unfold mechanicalLetter
  by_cases he : mechanicalFloor a t (j + 1) = mechanicalFloor a t j + 1
  · simp [he]
  · simp only [he, decide_false, Bool.false_eq_true, if_false, add_zero]
    omega

private theorem mechanicalLetter_int_shift (a t : ℝ) (q : ℤ) (j : Nat) :
    mechanicalLetter a (t + q) j = mechanicalLetter a t j := by
  unfold mechanicalLetter mechanicalFloor
  have he (l : Nat) : t + q + (l : ℝ) * a = (t + (l : ℝ) * a) + q := by ring
  simp only [he, Int.floor_add_intCast]
  rw [decide_eq_decide]
  omega

/-- A factor starting at i is the prefix for the corresponding
fractional intercept. -/
theorem characteristic_window_eq_fract (a : ℝ) (i k : Nat) :
    window (characteristicWord a) k i =
      fun (j : Fin k) => mechanicalLetter a (Int.fract (a + (i : ℝ) * a)) j.val := by
  funext j
  change mechanicalLetter a a (i + j.val) =
    mechanicalLetter a (Int.fract (a + (i : ℝ) * a)) j
  calc
    _ = mechanicalLetter a (a + (i : ℝ) * a) j := by
      unfold mechanicalLetter mechanicalFloor
      push_cast
      congr 1
      congr 1 <;> ring_nf
    _ = _ := by
      symm
      unfold Int.fract
      rw [sub_eq_add_neg, ← Int.cast_neg, mechanicalLetter_int_shift]

/-- Equal mechanical prefixes based at normalized intercepts have identical
cumulative floors at every position within the prefix. -/
theorem mechanicalFloor_eq_of_same_prefix {a t s : ℝ} {k : Nat}
    (ha : 0 < a) (ha' : a < 1) (ht : 0 ≤ t) (ht' : t < 1)
    (hs : 0 ≤ s) (hs' : s < 1)
    (h : ∀ j < k, mechanicalLetter a t j = mechanicalLetter a s j) :
    ∀ j ≤ k, mechanicalFloor a t j = mechanicalFloor a s j := by
  intro j
  induction j with
  | zero =>
    intro _
    have ht0 := Int.floor_eq_zero_iff.mpr ⟨ht, ht'⟩
    have hs0 := Int.floor_eq_zero_iff.mpr ⟨hs, hs'⟩
    simpa [mechanicalFloor] using ht0.trans hs0.symm
  | succ j ih =>
    intro hj
    rw [mechanicalFloor_step_eq _ _ _ ha ha', mechanicalFloor_step_eq _ _ _ ha ha',
      ih (by omega), h j (by omega)]

private noncomputable def rightCut (a : ℝ) (k : Nat) : ℝ :=
  1 - Int.fract (((k + 1 : Nat) : ℝ) * a)

private theorem floor_at_rightCut {a t s : ℝ} {k : Nat}
    (ht : 0 ≤ t) (hs : s < 1) (hts : t ≤ s)
    (hprefix : ∀ j ≤ k, mechanicalFloor a t j = mechanicalFloor a s j)
    (hnext : mechanicalFloor a t (k + 1) ≠ mechanicalFloor a s (k + 1)) :
    ∀ j ≤ k, mechanicalFloor a (rightCut a k) j = mechanicalFloor a t j := by
  let z := ((k + 1 : Nat) : ℝ) * a
  have hb₁ : ⌊z⌋ ≤ mechanicalFloor a t (k + 1) := by
    apply Int.floor_mono
    change z ≤ t + z
    linarith
  have hb₂ : mechanicalFloor a s (k + 1) ≤ ⌊z⌋ + 1 := by
    rw [← Int.floor_add_one]
    apply Int.floor_mono
    change s + z ≤ z + 1
    linarith
  have hm : mechanicalFloor a t (k + 1) ≤ mechanicalFloor a s (k + 1) :=
    Int.floor_mono (add_le_add_right hts z)
  have ht₀ : mechanicalFloor a t (k + 1) = ⌊z⌋ := by omega
  have hs₀ : mechanicalFloor a s (k + 1) = ⌊z⌋ + 1 := by omega
  have ht' := Int.lt_floor_add_one (t + z)
  change t + z < (mechanicalFloor a t (k + 1) : ℝ) + 1 at ht'
  rw [ht₀] at ht'
  have hs' := Int.floor_le (s + z)
  change (mechanicalFloor a s (k + 1) : ℝ) ≤ s + z at hs'
  rw [hs₀, Int.cast_add, Int.cast_one] at hs'
  have htcut : t ≤ rightCut a k := by
    change t ≤ 1 - (z - (⌊z⌋ : ℝ))
    linarith
  have hcuts : rightCut a k ≤ s := by
    change 1 - (z - (⌊z⌋ : ℝ)) ≤ s
    linarith
  intro j hj
  have hl : mechanicalFloor a t j ≤ mechanicalFloor a (rightCut a k) j :=
    Int.floor_mono (add_le_add_right htcut _)
  have hr : mechanicalFloor a (rightCut a k) j ≤ mechanicalFloor a s j :=
    Int.floor_mono (add_le_add_right hcuts _)
  rw [← hprefix j hj] at hr
  exact le_antisymm hr hl

private theorem floor_at_cut_eq {a : ℝ} (ha : Irrational a) (k j : Nat) (hj : j ≤ k) :
    mechanicalFloor a (rightCut a k) j =
      ⌊((k + 1 : Nat) : ℝ) * a⌋ - ⌊((k + 1 - j : Nat) : ℝ) * a⌋ := by
  let z := ((k + 1 : Nat) : ℝ) * a
  let y := ((k + 1 - j : Nat) : ℝ) * a
  have hy : Irrational y := irrational_natCast_mul_iff.2 ⟨by omega, ha⟩
  have he : rightCut a k + (j : ℝ) * a = -y + ((⌊z⌋ + 1 : ℤ) : ℝ) := by
    change 1 - (z - (⌊z⌋ : ℝ)) + (j : ℝ) * a = -y + ((⌊z⌋ + 1 : ℤ) : ℝ)
    have hyCast : y = (((k + 1 : Nat) : ℝ) - (j : ℝ)) * a :=
      congrArg (· * a) (Nat.cast_sub (show j ≤ k + 1 by omega))
    rw [Int.cast_add, Int.cast_one, hyCast]
    change 1 - (((k + 1 : Nat) : ℝ) * a - (⌊z⌋ : ℝ)) + (j : ℝ) * a = _
    ring
  unfold mechanicalFloor
  rw [he, Int.floor_add_intCast, Int.floor_neg]
  have hy' : ⌈y⌉ = ⌊y⌋ + 1 :=
    (Int.ceil_eq_floor_add_one_iff_not_mem y).2 (fun ⟨q, hq⟩ => hy.ne_int q hq.symm)
  rw [hy']
  change -(⌊y⌋ + 1) + (⌊z⌋ + 1) = ⌊z⌋ - ⌊y⌋
  omega

private theorem mechanicalLetter_at_cut {a : ℝ} (ha : Irrational a) (k j : Nat) (hj : j < k) :
    mechanicalLetter a (rightCut a k) j = characteristicWord a (k - 1 - j) := by
  unfold characteristicWord mechanicalLetter
  rw [floor_at_cut_eq ha k j (by omega), floor_at_cut_eq ha k (j + 1) (by omega)]
  have he (i : Nat) : mechanicalFloor a a i = ⌊((i + 1 : Nat) : ℝ) * a⌋ := by
    unfold mechanicalFloor
    push_cast
    congr 1
    ring
  rw [he, he, show k + 1 - (j + 1) = (k - 1 - j) + 1 by omega,
    show k + 1 - j = ((k - 1 - j) + 1) + 1 by omega]
  rw [decide_eq_decide]
  omega

private theorem mechanical_prefix_at_rightCut {a t s : ℝ} {k : Nat}
    (ha : 0 < a) (ha' : a < 1) (ht : 0 ≤ t) (ht' : t < 1) (hs : 0 ≤ s) (hs' : s < 1)
    (hprefix : ∀ j < k, mechanicalLetter a t j = mechanicalLetter a s j)
    (hnext : mechanicalLetter a t k ≠ mechanicalLetter a s k) :
    ∀ j < k, mechanicalLetter a (rightCut a k) j = mechanicalLetter a t j := by
  have hsame := mechanicalFloor_eq_of_same_prefix ha ha' ht ht' hs hs' hprefix
  have hdiff : mechanicalFloor a t (k + 1) ≠ mechanicalFloor a s (k + 1) := by
    intro he
    apply hnext
    unfold mechanicalLetter
    rw [he, hsame k le_rfl]
  have hcut : ∀ j ≤ k, mechanicalFloor a (rightCut a k) j = mechanicalFloor a t j := by
    rcases le_total t s with hts | hst
    · exact floor_at_rightCut ht hs' hts hsame hdiff
    · intro j hj
      rw [floor_at_rightCut hs ht' hst (fun l hl => (hsame l hl).symm) hdiff.symm j hj,
        hsame j hj]
  intro j hj
  unfold mechanicalLetter
  rw [hcut j (by omega), hcut (j + 1) (by omega)]

/-- A right-special factor contains the threshold at which its two
right extensions split. At that threshold its prefix is read backwards
from the characteristic word, giving the cited property (F2). -/
theorem characteristic_rightSpecial_eq_reversedPrefix {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a) (k : Nat)
    (u : Fin k → Bool) (hu : u ∈ rightSpecials (characteristicWord a) k) :
    List.ofFn u = reversedPrefix (characteristicWord a) k := by
  have hcard := (Finset.mem_filter.1 hu).2
  have htwo : 1 < (children (characteristicWord a) k u).card := by omega
  obtain ⟨v, z, hv, hz, hvz⟩ := Finset.one_lt_card_iff.1 htwo
  obtain ⟨hv, hpv⟩ := Finset.mem_filter.1 hv
  obtain ⟨hz, hpz⟩ := Finset.mem_filter.1 hz
  obtain ⟨i, hi⟩ := (mem_factorLanguage _ _ _).1 hv
  obtain ⟨l, hl⟩ := (mem_factorLanguage _ _ _).1 hz
  let t := Int.fract (a + (i : ℝ) * a)
  let s := Int.fract (a + (l : ℝ) * a)
  have hvt : v = fun (j : Fin (k + 1)) => mechanicalLetter a t j.val :=
    hi.symm.trans (characteristic_window_eq_fract a i (k + 1))
  have hzs : z = fun (j : Fin (k + 1)) => mechanicalLetter a s j.val :=
    hl.symm.trans (characteristic_window_eq_fract a l (k + 1))
  have hprefix₁ (j : Nat) (hj : j < k) : mechanicalLetter a t j = u ⟨j, hj⟩ := by
    rw [hvt] at hpv
    exact congrFun hpv ⟨j, hj⟩
  have hprefix₂ (j : Nat) (hj : j < k) : mechanicalLetter a s j = u ⟨j, hj⟩ := by
    rw [hzs] at hpz
    exact congrFun hpz ⟨j, hj⟩
  have hnext : mechanicalLetter a t k ≠ mechanicalLetter a s k := by
    intro he
    apply hvz
    funext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · rw [hvt, hzs]
      exact (hprefix₁ _ j.isLt).trans (hprefix₂ _ j.isLt).symm
    · rw [hvt, hzs]
      exact he
  have hcut := mechanical_prefix_at_rightCut ha ha' (Int.fract_nonneg _) (Int.fract_lt_one _)
    (Int.fract_nonneg _) (Int.fract_lt_one _)
    (fun j hj => (hprefix₁ j hj).trans (hprefix₂ j hj).symm) hnext
  apply List.ext_getElem
  · simp [reversedPrefix]
  intro j hj _
  have hj' : j < k := by simpa using hj
  simp only [List.getElem_ofFn, reversedPrefix, List.getElem_reverse, List.length_map,
    List.length_range, List.getElem_map, List.getElem_range]
  exact (hprefix₁ j hj').symm.trans ((hcut j hj').symm.trans
    (by simpa [Nat.sub_right_comm] using mechanicalLetter_at_cut hirr k j hj'))

/-- An eventual period would force the slope times the period to be
an integer, since the error in a cumulative floor count stays bounded. -/
theorem characteristic_not_eventually_periodic {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a) :
    ¬ ∃ i m : Nat, 0 < m ∧ ∀ t, characteristicWord a (i + t + m) = characteristicWord a (i + t) := by
  rintro ⟨i, m, hm, hp⟩
  let F := mechanicalFloor a a
  let C := F (i + m) - F i
  have hdiff (t : Nat) : F (i + t + m) - F (i + t) = C := by
    induction t with
    | zero => simp [C]
    | succ t ih =>
      have he₀ : i + (t + 1) = i + t + 1 := by omega
      have he₁ : i + (t + 1) + m = i + t + m + 1 := by omega
      change F (i + (t + 1) + m) - F (i + (t + 1)) = C
      rw [he₁, he₀]
      have hstep (j : Nat) : F (j + 1) = F j + if characteristicWord a j then 1 else 0 :=
        mechanicalFloor_step_eq a a j ha ha'
      rw [hstep, hstep, hp]
      omega
  have hmul (l : Nat) : F (i + l * m) - F i = (l : ℤ) * C := by
    induction l with
    | zero => simp
    | succ l ih =>
      have he : i + (l + 1) * m = i + l * m + m := by rw [Nat.succ_mul, Nat.add_assoc]
      change F (i + (l + 1) * m) - F i = ((l + 1 : Nat) : ℤ) * C
      rw [he, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      have h := hdiff (l * m)
      omega
  let δ := (m : ℝ) * a - (C : ℝ)
  have hbound (l : Nat) : |(l : ℝ) * δ| < 1 := by
    let x := a + (i : ℝ) * a
    let y := a + ((i + l * m : Nat) : ℝ) * a
    have hC : (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) = (l : ℝ) * (C : ℝ) := by
      exact_mod_cast hmul l
    have hyx : y - x = (l : ℝ) * ((m : ℝ) * a) := by
      change (a + ((i + l * m : Nat) : ℝ) * a) - (a + (i : ℝ) * a) = _
      push_cast
      ring
    have hfrac : (l : ℝ) * δ = Int.fract y - Int.fract x := by
      change (l : ℝ) * ((m : ℝ) * a - (C : ℝ)) = (y - (⌊y⌋ : ℝ)) - (x - (⌊x⌋ : ℝ))
      rw [mul_sub, ← hyx, ← hC]
      ring
    rw [hfrac, abs_lt]
    exact ⟨by linarith [Int.fract_nonneg y, Int.fract_lt_one x],
      by linarith [Int.fract_nonneg x, Int.fract_lt_one y]⟩
  have hzero : δ = 0 := by
    by_contra hne
    have hpos : 0 < |δ| := abs_pos.mpr hne
    obtain ⟨l, hl⟩ := exists_nat_gt (1 / |δ|)
    have hh := (div_lt_iff₀ hpos).1 hl
    have h := hbound l
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg l)] at h
    exact (not_lt_of_ge hh.le) h
  exact (irrational_natCast_mul_iff.2 ⟨hm.ne', hirr⟩).ne_int C (sub_eq_zero.mp hzero)

end Thesis.FactorTree
