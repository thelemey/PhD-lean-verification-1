import Thesis.FibonacciRichness
import Thesis.FibonacciCentralPrefixes
import Thesis.FibonacciBinet
import Thesis.SturmianMechanical
import Mathlib.Data.Real.GoldenRatio

open scoped goldenRatio

namespace Thesis.Fibonacci

noncomputable def mechanicalSlope : ℝ := 1 / φ ^ 2

private theorem slope_complement : mechanicalSlope + φ⁻¹ = 1 := by
  rw [mechanicalSlope, one_div, ← inv_pow,
    golden_inverse_square gold_add_goldConj gold_mul_goldConj, inv_gold]
  linarith [gold_add_goldConj]

theorem mechanicalSlope_pos : 0 < mechanicalSlope := by unfold mechanicalSlope; positivity

theorem mechanicalSlope_lt_one : mechanicalSlope < 1 := by
  have h := inv_pos.2 gold_pos
  linarith [slope_complement]

theorem mechanicalSlope_irrational : Irrational mechanicalSlope := by
  rw [show mechanicalSlope = 1 - φ⁻¹ by linarith [slope_complement]]
  simpa using gold_irrational.inv.ratCast_sub 1

/-- The characteristic mechanical word for the golden slope,
with false and true spelled a and b. -/
noncomputable def mechanicalWord (i : Nat) : Letter :=
  if FactorTree.characteristicWord mechanicalSlope i then .b else .a

private noncomputable def mechanicalCount (n : Nat) : ℤ :=
  ⌊((n : ℝ) + 1) * mechanicalSlope⌋

private noncomputable def complementCount (n : Nat) : Nat :=
  ⌊((n : ℝ) + 1) * φ⁻¹⌋₊

private theorem mechanicalCount_step (n : Nat) :
    mechanicalCount (n + 1) =
      mechanicalCount n + if mechanicalWord n = .b then 1 else 0 := by
  have hα := mechanicalSlope_pos
  have hα' := mechanicalSlope_lt_one
  have he : mechanicalCount (n + 1) = ⌊((n : ℝ) + 2) * mechanicalSlope⌋ := by
    unfold mechanicalCount
    push_cast
    congr 1
    ring
  have h₁ : mechanicalCount n ≤ mechanicalCount (n + 1) := by
    rw [he]
    apply Int.floor_mono
    linarith
  have h₂ : mechanicalCount (n + 1) ≤ mechanicalCount n + 1 := by
    rw [he, Int.floor_le_iff]
    push_cast
    unfold mechanicalCount
    linarith [Int.lt_floor_add_one (((n : ℝ) + 1) * mechanicalSlope)]
  unfold mechanicalWord
  rw [FactorTree.characteristic_letter_floor_eq, ← he]
  change _ = mechanicalCount n +
    if (if decide (mechanicalCount (n + 1) = mechanicalCount n + 1) then Letter.b else .a) =
      Letter.b then 1 else 0
  by_cases h : mechanicalCount (n + 1) = mechanicalCount n + 1
  · simp [h]
  · simp [h]
    omega

private theorem counts_complement (n : Nat) :
    mechanicalCount n = (n : ℤ) - (complementCount n : ℤ) := by
  let y := ((n : ℝ) + 1) * φ⁻¹
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hl : (complementCount n : ℝ) < y := by
    apply lt_of_le_of_ne (Nat.floor_le hy)
    intro he
    have hirr : Irrational y := by
      dsimp [y]
      rw [← Nat.cast_add_one]
      exact gold_irrational.inv.natCast_mul (Nat.succ_ne_zero n)
    exact hirr.ne_nat _ he.symm
  have hu : y < (complementCount n : ℝ) + 1 := Nat.lt_floor_add_one _
  have he : ((n : ℝ) + 1) * mechanicalSlope + y = (n : ℝ) + 1 := by
    dsimp [y]
    rw [← mul_add, slope_complement, mul_one]
  apply Int.floor_eq_iff.2
  push_cast
  exact ⟨by linarith, by linarith⟩

private noncomputable def imageOffset (n : Nat) : Nat := n + complementCount n

private theorem imageOffset_zero : imageOffset 0 = 0 := by
  unfold imageOffset complementCount
  simpa only [Nat.cast_zero, zero_add, one_mul] using
    (Nat.floor_eq_zero).2 (inv_lt_one_of_one_lt₀ one_lt_gold)

private theorem imageOffset_step (n : Nat) :
    imageOffset (n + 1) = imageOffset n + if mechanicalWord n = .b then 1 else 2 := by
  have h := mechanicalCount_step n
  rw [counts_complement, counts_complement, Nat.cast_add, Nat.cast_one] at h
  unfold imageOffset
  split_ifs at h ⊢ <;> omega

private theorem count_at_imageOffset (n j : Nat) (hj : j ≤ 1) :
    mechanicalCount (imageOffset n + j) = complementCount n := by
  have hβ : 0 < φ⁻¹ := inv_pos.2 gold_pos
  have hα := mechanicalSlope_pos
  have hscale : (1 + φ⁻¹) * mechanicalSlope = φ⁻¹ := by
    have he : 1 + φ⁻¹ = φ := by rw [inv_gold]; linarith [gold_add_goldConj]
    rw [he]
    unfold mechanicalSlope
    field_simp [gold_ne_zero]
    ring
  let y := ((n : ℝ) + 1) * φ⁻¹
  let r := y - (complementCount n : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hr₀ : 0 ≤ r := sub_nonneg.2 (Nat.floor_le hy)
  have hr₁ : r < 1 := (sub_lt_iff_lt_add).2 (by
    simpa only [add_comm] using (Nat.lt_floor_add_one y))
  have hjR : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have he : (((imageOffset n + j : Nat) : ℝ) + 1) * mechanicalSlope =
      (complementCount n : ℝ) + r * φ⁻¹ + (j : ℝ) * mechanicalSlope := by
    unfold imageOffset
    push_cast
    dsimp only [r, y]
    linear_combination ((n : ℝ) + 1) * hscale -
      (((n : ℝ) + 1) * φ⁻¹ - complementCount n) * slope_complement
  unfold mechanicalCount
  rw [he]
  apply Int.floor_eq_iff.2
  push_cast
  have hl := mul_lt_mul_of_pos_right hr₁ hβ
  have hu := mul_le_mul_of_nonneg_right hjR hα.le
  have hr := mul_nonneg hr₀ hβ.le
  have hjα := mul_nonneg (Nat.cast_nonneg j) hα.le
  exact ⟨by linarith, by linarith [slope_complement]⟩

private theorem image_initial_letter (n : Nat) : mechanicalWord (imageOffset n) = .a := by
  have h := mechanicalCount_step (imageOffset n)
  rw [count_at_imageOffset n 1 le_rfl,
    show imageOffset n = imageOffset n + 0 by omega, count_at_imageOffset n 0 (by omega)] at h
  cases he : mechanicalWord (imageOffset n) <;> simp [he] at h ⊢

private theorem image_final_letter (n : Nat) (hn : mechanicalWord n = .a) :
    mechanicalWord (imageOffset n + 1) = .b := by
  have hd := mechanicalCount_step n
  simp [hn] at hd
  rw [counts_complement, counts_complement, Nat.cast_add, Nat.cast_one] at hd
  have hstep := imageOffset_step n
  simp [hn] at hstep
  have he := mechanicalCount_step (imageOffset n + 1)
  rw [show imageOffset n + 1 + 1 = imageOffset (n + 1) by omega,
    show imageOffset (n + 1) = imageOffset (n + 1) + 0 by omega,
    count_at_imageOffset (n + 1) 0 (by omega), count_at_imageOffset n 1 le_rfl] at he
  cases hg : mechanicalWord (imageOffset n + 1) with
  | a =>
    simp [hg] at he
    omega
  | b => rfl

private def letterPrefix (w : Nat → Letter) (n : Nat) : List Letter := List.ofFn fun i : Fin n => w i

private theorem prefix_succ (w : Nat → Letter) (n : Nat) :
    letterPrefix w (n + 1) = letterPrefix w n ++ [w n] := by
  simpa [letterPrefix, List.concat_eq_append] using
    (List.ofFn_succ' (fun i : Fin (n + 1) => w i.val))

private theorem prefix_length (w : Nat → Letter) (n : Nat) : (letterPrefix w n).length = n := by
  simp [letterPrefix]

/-- Applying the substitution to a finite prefix gives the corresponding
prefix at the next substitution scale. -/
private theorem image_prefix (n : Nat) :
    fibonacciMorphism (letterPrefix mechanicalWord n) = letterPrefix mechanicalWord (imageOffset n) := by
  induction n with
  | zero =>
    rw [imageOffset_zero]
    rfl
  | succ n ih =>
    rw [prefix_succ, fibonacciMorphism_append, ih, imageOffset_step]
    cases hw : mechanicalWord n
    · simp only [hw, reduceCtorEq, if_false]
      rw [show imageOffset n + 2 = (imageOffset n + 1) + 1 by omega, prefix_succ, prefix_succ,
        image_initial_letter n, image_final_letter n hw, List.append_assoc]
      rfl
    · simp only [hw, if_true]
      rw [prefix_succ, image_initial_letter n]
      rfl

/-- Proposition prop:mech for the word defined by the finite recurrence. -/
theorem infiniteWord_eq_mechanicalWord : infiniteWord = mechanicalWord := by
  have hprefix (n : Nat) : word n = letterPrefix mechanicalWord (word n).length := by
    induction n with
    | zero =>
      have h0 := image_initial_letter 0
      rw [imageOffset_zero] at h0
      change [.a] = letterPrefix mechanicalWord 1
      rw [prefix_succ, h0]
      rfl
    | succ n ih =>
      have hc : word (n + 1) = letterPrefix mechanicalWord (imageOffset (word n).length) := by
        rw [word_succ_eq_morphism, ← image_prefix, ← ih]
      have hl := congrArg List.length hc
      rw [prefix_length] at hl
      simpa only [← hl] using hc
  funext i
  have he := congrArg (fun xs : List Letter => xs[i]?) (hprefix i)
  have hi := word_covers i
  have hr : i < (letterPrefix mechanicalWord (word i).length).length := by
    rw [prefix_length]
    exact hi
  change (word i)[i]? = (letterPrefix mechanicalWord (word i).length)[i]? at he
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hr] at he
  simpa [infiniteWord, WordPrefixLimits.prefixLimit, letterPrefix] using Option.some.inj he

theorem infiniteWord_letter_floor (i : Nat) :
    infiniteWord i = .b ↔
      ⌊((i : ℝ) + 2) * mechanicalSlope⌋ = ⌊((i : ℝ) + 1) * mechanicalSlope⌋ + 1 := by
  rw [infiniteWord_eq_mechanicalWord]
  simp [mechanicalWord, FactorTree.characteristic_letter_floor_eq]

/-- The length-`k` factor starting at position `i` (zero based). -/
def factorWindow (i k : Nat) : List Letter := letterPrefix (fun j => infiniteWord (i + j)) k

@[simp] theorem factorWindow_length (i k : Nat) : (factorWindow i k).length = k :=
  prefix_length _ _

private theorem factorWindow_count_complement (i k : Nat) :
    (factorWindow i k).count .a + (factorWindow i k).count .b = k := by
  have h (xs : List Letter) : xs.count .a + xs.count .b = xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => cases x <;> simp [List.count_cons] <;> omega
  simpa using h (factorWindow i k)

/-- Telescoping the mechanical letters over a finite window. -/
theorem factorWindow_count_b (i k : Nat) :
    ((factorWindow i k).count .b : ℤ) =
      ⌊((i : ℝ) + 1) * mechanicalSlope + (k : ℝ) * mechanicalSlope⌋ -
        ⌊((i : ℝ) + 1) * mechanicalSlope⌋ := by
  have hcount : ((factorWindow i k).count .b : ℤ) = mechanicalCount (i + k) - mechanicalCount i := by
    induction k with
    | zero => simp [factorWindow, letterPrefix]
    | succ k ih =>
      have hs : factorWindow i (k + 1) = factorWindow i k ++ [infiniteWord (i + k)] :=
        prefix_succ _ _
      rw [hs, List.count_append, Nat.cast_add, ih, ← Nat.add_assoc, mechanicalCount_step,
        infiniteWord_eq_mechanicalWord]
      cases h : mechanicalWord (i + k) <;> (simp [h] <;> omega)
  rw [hcount]
  unfold mechanicalCount
  push_cast
  rw [show ((i : ℝ) + (k : ℝ) + 1) * mechanicalSlope =
      ((i : ℝ) + 1) * mechanicalSlope + (k : ℝ) * mechanicalSlope by ring]

private theorem floor_sub_mem (x y : ℝ) (hy : Irrational y) :
    ⌊x + y⌋ - ⌊x⌋ = ⌊y⌋ ∨ ⌊x + y⌋ - ⌊x⌋ = ⌈y⌉ := by
  have hc : ⌈y⌉ = ⌊y⌋ + 1 := by
    apply Int.ceil_eq_iff.2
    push_cast
    exact ⟨by
      have h := lt_of_le_of_ne (Int.floor_le y) (Ne.symm (hy.ne_int ⌊y⌋))
      linarith, (Int.lt_floor_add_one y).le⟩
  have hlo := Int.le_floor_add x y
  have hhi := Int.le_floor_add_floor x y
  omega

/-- Complementary counts transfer floor and ceiling by exchanging the two. -/
private theorem floor_ceil_complement (k : ℤ) (x : ℝ) :
    ⌊(k : ℝ) - x⌋ = k - ⌈x⌉ ∧ ⌈(k : ℝ) - x⌉ = k - ⌊x⌋ := by
  constructor
  · rw [sub_eq_add_neg, Int.floor_intCast_add, Int.floor_neg]
    ring
  · rw [sub_eq_add_neg, add_comm, Int.ceil_add_intCast, Int.ceil_neg]
    ring

/-- The two possible counts of each letter in a factor, as in `prop:balance`. -/
theorem factorWindow_counts_balanced (i k : Nat) :
    let b : ℤ := (factorWindow i k).count .b
    let a : ℤ := (factorWindow i k).count .a
    (b = ⌊(k : ℝ) * mechanicalSlope⌋ ∨ b = ⌈(k : ℝ) * mechanicalSlope⌉) ∧
    (a = ⌊(k : ℝ) * φ⁻¹⌋ ∨ a = ⌈(k : ℝ) * φ⁻¹⌉) := by
  dsimp only
  by_cases hk : k = 0
  · subst k
    simp [factorWindow, letterPrefix]
  have hb := floor_sub_mem (((i : ℝ) + 1) * mechanicalSlope) ((k : ℝ) * mechanicalSlope)
    (mechanicalSlope_irrational.natCast_mul hk)
  rw [← factorWindow_count_b i k] at hb
  refine ⟨hb, ?_⟩
  have hs := congrArg (fun n : Nat => (n : ℤ)) (factorWindow_count_complement i k)
  push_cast at hs
  have he : (k : ℝ) * φ⁻¹ = ((k : ℤ) : ℝ) - (k : ℝ) * mechanicalSlope := by
    push_cast
    have hc : φ⁻¹ = 1 - mechanicalSlope := by linarith [slope_complement]
    rw [hc]
    ring
  rw [he]
  obtain ⟨hfloor, hceil⟩ := floor_ceil_complement (k : ℤ) ((k : ℝ) * mechanicalSlope)
  rw [hfloor, hceil]
  omega

private theorem abs_sub_lt_one_of_floor_or_ceil {z : ℤ} {x : ℝ}
    (hz : z = ⌊x⌋ ∨ z = ⌈x⌉) : |(z : ℝ) - x| < 1 := by
  rw [abs_lt]
  rcases hz with rfl | rfl
  · constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]
  · constructor <;> linarith [Int.le_ceil x, Int.ceil_lt_add_one x]

private theorem frequency_error {m : Nat} (hm : 0 < m) {z : ℤ} {slope : ℝ}
    (hz : z = ⌊(m : ℝ) * slope⌋ ∨ z = ⌈(m : ℝ) * slope⌉) :
    |(z : ℝ) / m - slope| < 1 / (m : ℝ) := by
  have hreal : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (z : ℝ) / m - slope = ((z : ℝ) - (m : ℝ) * slope) / m := by
    field_simp
  rw [he, abs_div, abs_of_pos hreal, div_lt_div_iff_of_pos_right hreal]
  exact abs_sub_lt_one_of_floor_or_ceil hz

theorem factorWindow_density_errors (i k : Nat) (hk : 0 < k) :
    |((factorWindow i k).count .b : ℝ) / k - mechanicalSlope| < 1 / (k : ℝ) ∧
    |((factorWindow i k).count .a : ℝ) / k - φ⁻¹| < 1 / (k : ℝ) := by
  have h := factorWindow_counts_balanced i k
  exact ⟨by simpa using frequency_error hk h.1, by simpa using frequency_error hk h.2⟩

end Thesis.Fibonacci
