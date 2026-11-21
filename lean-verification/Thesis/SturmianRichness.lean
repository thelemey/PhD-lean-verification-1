import Thesis.InfiniteRichness
import Thesis.PalindromicMorphismRichness
import Thesis.SturmianMechanical

namespace Thesis.FactorTree

open PalindromeFactors

/-- Number of ones in a characteristic prefix. Its use as an offset accounts
for the extra zero inserted before each one by the left Sturmian morphism. -/
private noncomputable def ones (b : ℝ) (m : Nat) : Nat := ⌊((m : ℝ)+1)*b⌋₊
/-- Length after applying 0 ↦ 0 and 1 ↦ 01 to the first m letters. -/
noncomputable def characteristicImageLength (b : ℝ) (m : Nat) : Nat := m + ones b m

private theorem floor_ones {b : ℝ} (hb : 0 < b) (m : Nat) :
    ⌊((m : ℝ)+1)*b⌋ = (ones b m : ℤ) := (Int.natCast_floor_eq_floor (by positivity)).symm

private theorem letter_ones {b : ℝ} (hb : 0 < b) (m : Nat) :
    characteristicWord b m = decide (ones b (m+1) = ones b m + 1) := by
  rw [characteristic_letter_floor_eq, decide_eq_decide, ← Nat.cast_inj (R := ℤ)]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← floor_ones hb, ← floor_ones hb]
  push_cast
  ring_nf

private theorem ones_step {b : ℝ} (hb : 0 < b) (hb' : b < 1) (m : Nat) :
    ones b (m+1) = ones b m + if characteristicWord b m then 1 else 0 := by
  have h₁ : ones b m ≤ ones b (m+1) := by
    unfold ones
    apply Nat.floor_mono
    push_cast
    linarith
  have hl := Nat.lt_floor_add_one (((m : ℝ)+1)*b)
  have hu := Nat.floor_le (show 0 ≤ (((m+1 : Nat) : ℝ)+1)*b by positivity)
  change ((ones b m : ℝ)+_) > _ at hl
  change (ones b (m+1) : ℝ) ≤ _ at hu
  push_cast at hu
  have h₂ : ones b (m+1) < ones b m + 2 := by
    exact_mod_cast (show (ones b (m+1) : ℝ) < (ones b m : ℝ)+2 by linarith)
  rw [letter_ones hb]
  by_cases he : ones b (m+1) = ones b m + 1 <;> simp [he]
  omega

/-- Both floor values at the first (zero) letter of a morphism block equal
the count of ones at the start of the original block. -/
private theorem ones_at_boundary {b : ℝ} (hb : 0 < b) (m d : Nat) (hd : d ≤ 1) :
    ones (b/(1+b)) (characteristicImageLength b m+d) = ones b m := by
  have hden : 0 < 1+b := by linarith
  have hlow := Nat.floor_le (show 0 ≤ ((m : ℝ)+1)*b by positivity)
  have hhigh := Nat.lt_floor_add_one (((m : ℝ)+1)*b)
  change (ones b m : ℝ) ≤ _ at hlow
  change _ < (ones b m : ℝ)+1 at hhigh
  have hd' : (d : ℝ) ≤ 1 := by exact_mod_cast hd
  have hdlo : 0 ≤ (d : ℝ)*b := by positivity
  have hdhi : (d : ℝ)*b ≤ b := by nlinarith only [mul_le_mul_of_nonneg_right hd' hb.le]
  change ⌊_⌋₊ = ones b m
  apply (Nat.floor_eq_iff (by positivity)).2
  simp only [characteristicImageLength, Nat.cast_add, ← mul_div_assoc]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith only [hlow, hdlo]
  · apply (div_lt_iff₀ hden).2
    nlinarith only [hhigh, hdhi]

private theorem letter_boundary {b : ℝ} (hb : 0 < b) (m : Nat) :
    characteristicWord (b/(1+b)) (characteristicImageLength b m) = false := by
  rw [letter_ones (by positivity), ones_at_boundary hb m 1 (by decide)]
  have h := ones_at_boundary hb m 0 (by decide)
  simp only [Nat.add_zero] at h
  simp [h]

private theorem letter_after_boundary {b : ℝ} (hb : 0 < b) (hb' : b < 1) (m : Nat)
    (h : characteristicWord b m = true) :
    characteristicWord (b/(1+b)) (characteristicImageLength b m+1) = true := by
  have hs := ones_step hb hb' m
  simp only [h, if_true] at hs
  have he : characteristicImageLength b m+1+1 = characteristicImageLength b (m+1) := by unfold characteristicImageLength; omega
  have hlast := ones_at_boundary hb (m+1) 0 (by decide)
  simp only [Nat.add_zero] at hlast
  rw [letter_ones (by positivity), he, hlast, ones_at_boundary hb m 1 (by decide)]
  simp [hs]

/-- Prefix form of the standard Sturmian morphism 0 ↦ 0, 1 ↦ 01.
The slope changes from b to b/(1+b). -/
theorem characteristic_leftMorphism_prefix {b : ℝ} (hb : 0 < b) (hb' : b < 1) (m : Nat) :
    leftPalMorphism false (factorList (characteristicWord b) 0 m) =
      factorList (characteristicWord (b/(1+b))) 0 (characteristicImageLength b m) := by
  induction m with
  | zero =>
    have hz : ones b 0 = 0 := by simpa [ones] using Nat.floor_eq_zero.mpr hb'
    simp [characteristicImageLength, hz, factorList, leftPalMorphism]
  | succ m ih =>
    rw [factorList_succ, Nat.zero_add, leftPalMorphism_append, ih]
    have hs := ones_step hb hb' m
    cases he : characteristicWord b m with
    | false =>
      simp only [he, Bool.false_eq_true, if_false, Nat.add_zero] at hs
      have ho : characteristicImageLength b (m+1) = characteristicImageLength b m+1 := by unfold characteristicImageLength; omega
      rw [ho, factorList_succ, Nat.zero_add, letter_boundary hb]
      rfl
    | true =>
      simp only [he, if_true] at hs
      have ho : characteristicImageLength b (m+1) = characteristicImageLength b m+1+1 := by unfold characteristicImageLength; omega
      rw [ho, factorList_succ, factorList_succ, Nat.zero_add, Nat.zero_add,
        letter_boundary hb, letter_after_boundary hb hb' m he]
      simp [leftPalMorphism, List.append_assoc]

private theorem reflected_floor {a : ℝ} (hi : Irrational a) (k : Nat) (hk : k ≠ 0) :
    ⌊(k : ℝ)*(1-a)⌋ = (k : ℤ) - ⌊(k : ℝ)*a⌋ - 1 := by
  have hir := hi.natCast_mul hk
  have hl := (Int.floor_le ((k : ℝ)*a)).lt_of_ne (hir.ne_int _).symm
  have hu := Int.lt_floor_add_one ((k : ℝ)*a)
  apply Int.floor_eq_iff.2
  push_cast
  constructor <;> linarith

/-- Exchanging the two letters reflects an irrational slope about 1/2. -/
theorem characteristicWord_one_sub {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hi : Irrational a)
    (m : Nat) : characteristicWord (1-a) m = !(characteristicWord a m) := by
  have f₁ := reflected_floor hi (m+1) (by omega)
  have f₂ := reflected_floor hi (m+2) (by omega)
  push_cast at f₁ f₂
  rw [characteristic_letter_floor_eq, f₂, f₁, floor_ones ha]
  have f := floor_ones ha (m+1)
  push_cast at f
  rw [show (m : ℝ)+2 = (m+1)+1 by ring, f]
  have hs := ones_step ha ha' m
  cases he : characteristicWord a m <;> simp [he] at hs ⊢ <;> omega

private def exchange : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

private theorem rich_small_slope {n : Nat}
    (ih : ∀ {b : ℝ}, 0 < b → b < 1 → Irrational b → Rich (factorList (characteristicWord b) 0 n))
    {a : ℝ} (ha : 0 < a) (half : a < 1/2) (hi : Irrational a) :
    Rich (factorList (characteristicWord a) 0 (n+1)) := by
  let b := a/(1-a)
  have hd : 0 < 1-a := by linarith
  have hb : 0 < b := div_pos ha hd
  have hb' : b < 1 := (div_lt_iff₀ hd).2 (by linarith)
  have hbI : Irrational b := by
    have he : b = (1-a)⁻¹-1 := by dsimp [b]; field_simp
    rw [he]
    simpa using ((hi.natCast_sub 1).inv.sub_natCast 1)
  have he : b/(1+b) = a := by dsimp [b]; field_simp
  have him := characteristic_leftMorphism_prefix hb hb' n
  rw [he] at him
  have hz := letter_boundary hb n
  rw [he] at hz
  have hr := rich_centeredPalImage false (ih hb hb' hbI)
  rw [centeredPalImage, him, ← hz, ← Nat.zero_add (characteristicImageLength b n)] at hr
  have hwhole : Rich (factorList (characteristicWord a) 0 (characteristicImageLength b n+1)) := by
    rw [factorList_succ, Nat.zero_add]
    simpa using hr
  exact rich_of_infix hwhole (factorList_prefix _ (by unfold characteristicImageLength; omega)).isInfix

/-- Richness of every finite factor of an irrational characteristic Sturmian
word, the classical input cited in thm:Yrich. The centered morphism image
covers one additional prefix letter, so induction on length suffices even
for arbitrarily long constant runs. -/
theorem characteristicWord_infiniteRich {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hi : Irrational a) :
    InfiniteRich (characteristicWord a) := by
  apply (infiniteRich_iff_prefixes _).2
  intro n
  induction n generalizing a with
  | zero =>
    exact ⟨[], ⟨by simp, fun v => by simp [factorList, PalindromicFactor]; tauto⟩, rfl⟩
  | succ n ih =>
    by_cases h : a < 1/2
    · exact rich_small_slope ih ha h hi
    have ha_ne : a ≠ 1/2 := by simpa using hi.ne_rat (1/2)
    have h' : 1-a < 1/2 := by rcases lt_or_gt_of_ne ha_ne with h₁ | h₁ <;> linarith
    have hr := rich_small_slope ih (a := 1-a) (by linarith) h' (by simpa using hi.natCast_sub 1)
    have he : (factorList (characteristicWord (1-a)) 0 (n+1)).map exchange =
        factorList (characteristicWord a) 0 (n+1) := by
      apply List.ext_getElem (by simp [factorList])
      intro j _ _
      simp only [List.getElem_map, factorList, List.getElem_ofFn, characteristicWord_one_sub ha ha' hi]
      exact Bool.not_not _
    exact he ▸ rich_rename exchange hr

end Thesis.FactorTree
