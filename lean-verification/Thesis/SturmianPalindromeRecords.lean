import Thesis.SturmianMechanical
import Thesis.Palindrome

namespace Thesis.SturmianDensity

private def bitCount (b : Bool) : ℤ := if b then 1 else 0

private theorem bitCount_injective : Function.Injective bitCount := by
  intro b c
  cases b <;> cases c <;> simp [bitCount]

/-- A palindrome has the same number of ones in corresponding initial
and final intervals. Conversely these counts determine the letters. -/
private theorem palPrefix_iff_symmetric_counts (w : Nat → Bool) (F : Nat → ℤ)
    (hstep : ∀ i, F (i + 1) = F i + bitCount (w i)) (n : Nat) :
    PalPrefix w n ↔ ∀ j ≤ n, F j + F (n - j) = F 0 + F n := by
  constructor
  · intro h j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have h₁ := hstep j
      have h₂ := hstep (n - (j + 1))
      have hsub : n - (j + 1) + 1 = n - j := by omega
      have hind := ih (by omega)
      have he := h j (by omega)
      rw [show n - 1 - j = n - (j + 1) by omega] at he
      rw [← he, hsub] at h₂
      change F (j + 1) + F (n - (j + 1)) = F 0 + F n
      omega
  · intro h j hj
    have h₀ := h j hj.le
    have h₁ := h (j + 1) (by omega)
    have hL := hstep j
    have hR := hstep (n - (j + 1))
    rw [show n - (j + 1) + 1 = n - j by omega] at hR
    change w j = w (n - 1 - j)
    rw [show n - 1 - j = n - (j + 1) by omega]
    apply bitCount_injective
    omega

private noncomputable def prefixFloor (a : ℝ) (i : Nat) : ℤ := ⌊((i : ℝ) + 1) * a⌋

private theorem prefixFloor_step {a : ℝ} (ha : 0 < a) (ha' : a < 1) (i : Nat) :
    prefixFloor a (i + 1) = prefixFloor a i + bitCount (FactorTree.characteristicWord a i) := by
  let X : ℝ := ((i : ℝ) + 1) * a
  let Y : ℝ := ((i : ℝ) + 2) * a
  have h₁ : ⌊X⌋ ≤ ⌊Y⌋ := Int.floor_mono (by dsimp [X, Y]; linarith)
  have h₂ : ⌊Y⌋ ≤ ⌊X⌋ + 1 := by
    rw [Int.floor_le_iff]
    push_cast
    have := Int.lt_floor_add_one X
    dsimp [X, Y] at *
    linarith
  have he : prefixFloor a (i + 1) = ⌊Y⌋ := by
    unfold prefixFloor
    push_cast
    congr 1
    dsimp [Y]
    ring
  rw [he, FactorTree.characteristic_letter_floor_eq]
  change ⌊Y⌋ = ⌊X⌋ + bitCount (decide (⌊Y⌋ = ⌊X⌋ + 1))
  by_cases h : ⌊Y⌋ = ⌊X⌋ + 1
  · simp [bitCount, h]
  · simp only [bitCount, h, decide_false, Bool.false_eq_true, if_false, add_zero]
    omega

private theorem floor_sum_carry (x y : ℝ) :
    ⌊x⌋ + ⌊y⌋ = ⌊x + y⌋ - if Int.fract (x + y) < Int.fract x then 1 else 0 := by
  have hlo := Int.le_floor_add x y
  have hhi := Int.le_floor_add_floor x y
  have hX := Int.floor_add_fract x
  have hY := Int.floor_add_fract y
  have hXY := Int.floor_add_fract (x + y)
  by_cases h : ⌊x⌋ + ⌊y⌋ = ⌊x + y⌋
  · have hr : (⌊x⌋ : ℝ) + (⌊y⌋ : ℝ) = (⌊x + y⌋ : ℝ) := by exact_mod_cast h
    have hnot : ¬Int.fract (x + y) < Int.fract x := by linarith [Int.fract_nonneg y]
    simpa [hnot] using h
  · have he : ⌊x⌋ + ⌊y⌋ = ⌊x + y⌋ - 1 := by omega
    have hr : (⌊x⌋ : ℝ) + (⌊y⌋ : ℝ) = (⌊x + y⌋ : ℝ) - 1 := by exact_mod_cast he
    have hlt : Int.fract (x + y) < Int.fract x := by linarith [Int.fract_lt_one y]
    simpa [hlt] using he

private theorem prefixFloor_carry (a : ℝ) {j n : Nat} (hj : j ≤ n) :
    prefixFloor a j + prefixFloor a (n - j) =
      ⌊((n : ℝ) + 2) * a⌋ -
        if Int.fract (((n : ℝ) + 2) * a) < Int.fract (((j : ℝ) + 1) * a) then 1 else 0 := by
  have he : ((j : ℝ) + 1) * a + (((n - j : Nat) : ℝ) + 1) * a = ((n : ℝ) + 2) * a := by
    rw [Nat.cast_sub hj]
    ring
  have h := floor_sum_carry (((j : ℝ) + 1) * a) ((((n - j : Nat) : ℝ) + 1) * a)
  rw [he] at h
  exact h

private theorem frac_natMul_injective {a : ℝ} (ha : Irrational a) :
    Function.Injective (fun j : Nat => Int.fract ((j : ℝ) * a)) := by
  intro j k he
  by_contra hn
  have hne : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 he
  have hI := irrational_intCast_mul_iff.2 ⟨hne, ha⟩
  apply hI.ne_int z
  calc
    (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * a = (j : ℝ) * a - (k : ℝ) * a := by push_cast; ring
    _ = z := hz

/-- A characteristic Sturmian prefix of length n is palindromic exactly
when the fractional part at time n+2 is a new minimum or maximum.
This is the rotation criterion underlying the length enumeration. -/
theorem characteristic_palPrefix_iff_fractional_record {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hirr : Irrational a) (n : Nat) :
    PalPrefix (FactorTree.characteristicWord a) n ↔
      (∀ j : Nat, 0 < j → j < n + 2 →
        Int.fract (((n + 2 : Nat) : ℝ) * a) < Int.fract ((j : ℝ) * a)) ∨
      (∀ j : Nat, 0 < j → j < n + 2 →
        Int.fract ((j : ℝ) * a) < Int.fract (((n + 2 : Nat) : ℝ) * a)) := by
  let T := Int.fract (((n : ℝ) + 2) * a)
  let f := fun j : Nat => Int.fract (((j : ℝ) + 1) * a)
  have hne (j : Nat) (hj : j ≤ n) : T ≠ f j := by
    intro he
    have he' : Int.fract (((n + 2 : Nat) : ℝ) * a) =
        Int.fract (((j + 1 : Nat) : ℝ) * a) := by simpa [T, f] using he
    have hh := frac_natMul_injective hirr he'
    omega
  have hcast : Int.fract (((n + 2 : Nat) : ℝ) * a) = T := by simp [T]
  rw [hcast, palPrefix_iff_symmetric_counts _ _ (prefixFloor_step ha ha') n]
  have carry (j : Nat) (hj : j ≤ n) :
      prefixFloor a j + prefixFloor a (n - j) =
        ⌊((n : ℝ) + 2) * a⌋ - if T < f j then 1 else 0 := prefixFloor_carry a hj
  constructor
  · intro h
    have hc0 := carry 0 (Nat.zero_le n)
    simp only [Nat.sub_zero] at hc0
    have compare (j : Nat) (hj : j ≤ n) :
        (if T < f j then (1 : ℤ) else 0) = (if T < f 0 then 1 else 0) := by
      have hc := carry j hj
      rw [h j hj, hc0] at hc
      omega
    by_cases h0 : T < f 0
    · left
      intro j hj hj'
      have hn : j - 1 ≤ n := by omega
      have hc := compare (j - 1) hn
      simp only [h0, if_true] at hc
      have ht : T < f (j - 1) := by
        by_cases h' : T < f (j - 1)
        · exact h'
        · rw [if_neg h'] at hc
          omega
      have hj'': (j - 1 : Nat) + 1 = j := by omega
      simpa only [f, ← Nat.cast_add_one, hj''] using ht
    · right
      intro j hj hj'
      have hn : j - 1 ≤ n := by omega
      have hc := compare (j - 1) hn
      simp only [h0, if_false] at hc
      have ht : f (j - 1) < T := by
        apply lt_of_le_of_ne _ (hne _ hn).symm
        exact le_of_not_gt (fun h' => by rw [if_pos h'] at hc; omega)
      have hj'' : (j - 1 : Nat) + 1 = j := by omega
      simpa only [f, ← Nat.cast_add_one, hj''] using ht
  · rintro (h | h) j hj
    · have hf (l : Nat) (hl : l ≤ n) : T < f l := by
        simpa only [f, Nat.cast_add_one] using h (l + 1) (by omega) (by omega)
      rw [carry j hj, if_pos (hf j hj)]
      simpa only [Nat.sub_zero, if_pos (hf 0 (Nat.zero_le n))] using
        (carry 0 (Nat.zero_le n)).symm
    · have hf (l : Nat) (hl : l ≤ n) : ¬ T < f l := by
        apply not_lt_of_ge
        have he := h (l + 1) (by omega) (by omega)
        simpa only [f, Nat.cast_add_one] using he.le
      rw [carry j hj, if_neg (hf j hj)]
      simpa only [Nat.sub_zero, if_neg (hf 0 (Nat.zero_le n))] using
        (carry 0 (Nat.zero_le n)).symm

end Thesis.SturmianDensity
