import Thesis.SturmianRichness
import Thesis.SturmianDiophantine

open Filter Set
open GenContFract

namespace Thesis.SturmianDensity

open FactorTree PalindromeFactors

private noncomputable def remainder (a : ℝ) : Nat → ℝ
  | 0 => a
  | n+1 => Int.fract (remainder a n)⁻¹

private theorem remainder_bounds {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hi : Irrational a)
    (n : Nat) : 0 < remainder a n ∧ remainder a n < 1 ∧ Irrational (remainder a n) := by
  induction n with
  | zero => exact ⟨ha,ha',hi⟩
  | succ n ih =>
    have hir : Irrational (Int.fract (remainder a n)⁻¹) := ih.2.2.inv.sub_intCast _
    exact ⟨(Int.fract_nonneg _).lt_of_ne (by simpa using (hir.ne_rat 0).symm), Int.fract_lt_one _, hir⟩

private theorem reciprocal_remainder {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hi : Irrational a)
    (k : Nat) : (remainder a k)⁻¹ = (partialQuotient a k : ℝ) + remainder a (k+1) := by
  have stream (n : Nat) : ∃ p, IntFractPair.stream a n = some p ∧ p.fr = remainder a n := by
    induction n with
    | zero => exact ⟨_, IntFractPair.stream_zero a, Int.fract_eq_self.2 ⟨ha.le,ha'⟩⟩
    | succ n ih =>
      obtain ⟨p,hp,hr⟩ := ih
      have hn := (remainder_bounds ha ha' hi n).1
      have he := IntFractPair.stream_succ_of_some hp (show p.fr ≠ 0 by rw [hr]; exact hn.ne')
      exact ⟨_, he, by rw [hr]; rfl⟩
  obtain ⟨p,hp,hr⟩ := stream k
  have hn := (remainder_bounds ha ha' hi k).1
  have he := IntFractPair.stream_succ_of_some hp (show p.fr ≠ 0 by rw [hr]; exact hn.ne')
  rw [hr] at he
  have hf : 0 ≤ ⌊(remainder a k)⁻¹⌋ := Int.floor_nonneg.2 (inv_nonneg.2 hn.le)
  have hq : (partialQuotient a k : ℤ) = ⌊(remainder a k)⁻¹⌋ := by
    unfold partialQuotient
    rw [he]
    exact Int.toNat_of_nonneg hf
  have hq' : (partialQuotient a k : ℝ) = (⌊(remainder a k)⁻¹⌋ : ℤ) := by exact_mod_cast hq
  rw [hq']
  change _ = _ + Int.fract (remainder a k)⁻¹
  exact (Int.floor_add_fract _).symm

/-- The morphism sending 0 to a block of d zeros followed by 1, and 1 to 0. -/
def standardMorphism : Nat → List Bool → List Bool
  | 0, w => w.map Bool.not
  | d+1, w => leftPalMorphism false (standardMorphism d w)

private theorem morphism_append (d : Nat) (v w : List Bool) :
    standardMorphism d (v++w) = standardMorphism d v ++ standardMorphism d w := by
  induction d with
  | zero => simp [standardMorphism]
  | succ d ih => simp [standardMorphism, ih, leftPalMorphism_append]

private theorem morphism_zero (d : Nat) : standardMorphism d [false] = List.replicate d false ++ [true] := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have fixed (n : Nat) : leftPalMorphism false (List.replicate n false) = List.replicate n false := by
      induction n with
      | zero => rfl
      | succ n ih => simpa [List.replicate_succ, leftPalMorphism] using congrArg (List.cons false) ih
    simp [standardMorphism, ih, leftPalMorphism_append, fixed, List.replicate_succ', List.append_assoc,
      show leftPalMorphism false [true] = [false,true] by rfl]

private theorem morphism_one (d : Nat) : standardMorphism d [true] = [false] := by
  induction d with
  | zero => rfl
  | succ d ih => rw [standardMorphism, ih]; rfl

private def MapsPrefixes (f : List Bool → List Bool) (b a : ℝ) : Prop :=
  ∀ n, ∃ k, f (factorList (characteristicWord b) 0 n) = factorList (characteristicWord a) 0 k

private theorem maps_standard (d : Nat) {b : ℝ} (hb : 0 < b) (hb' : b < 1) (hi : Irrational b) :
    MapsPrefixes (standardMorphism d) b ((1-b)/(1+d*(1-b))) := by
  induction d with
  | zero =>
    intro n
    refine ⟨n, ?_⟩
    simp only [Nat.cast_zero, zero_mul, add_zero, div_one, standardMorphism]
    apply List.ext_getElem (by simp [factorList])
    intro j _ _
    simp only [List.getElem_map, factorList, List.getElem_ofFn, characteristicWord_one_sub hb hb' hi]
  | succ d ih =>
    intro n
    obtain ⟨k,hk⟩ := ih n
    let u := (1-b)/(1+d*(1-b))
    have hb₀ : 0 < 1-b := by linarith
    have hden : 0 < 1+(d:ℝ)*(1-b) := by positivity
    have hu : 0 < u := div_pos hb₀ hden
    have hu' : u < 1 := (div_lt_iff₀ hden).2 (by nlinarith only [hb, mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) hb₀.le])
    have hz := characteristic_leftMorphism_prefix hu hu' k
    have hstep : u/(1+u) = (1-b)/(1+((d+1:Nat):ℝ)*(1-b)) := by
      dsimp only [u]
      push_cast
      field_simp
      left
      ring
    refine ⟨characteristicImageLength u k, ?_⟩
    rw [standardMorphism, hk, ← hstep]
    exact hz

/-- Directive exponents from proirrationaln1. The first quotient is reduced
by one, while the subsequent quotients enter unchanged. -/
noncomputable def directiveExponent (a : ℝ) : Nat → Nat
  | 0 => partialQuotient a 0 - 1
  | k+1 => partialQuotient a (k+1)

private noncomputable def tailSlope (a : ℝ) : Nat → ℝ
  | 0 => a
  | k+1 => remainder a (k+1) / (1+remainder a (k+1))

private theorem tail_bounds {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hi : Irrational a) (k : Nat) :
    0 < tailSlope a (k+1) ∧ tailSlope a (k+1) < 1/2 ∧ Irrational (tailSlope a (k+1)) := by
  let r := remainder a (k+1)
  obtain ⟨hr,hr',hir⟩ := remainder_bounds ha ha' hi (k+1)
  change 0 < r at hr
  change r < 1 at hr'
  change Irrational r at hir
  change 0 < r/(1+r) ∧ r/(1+r) < 1/2 ∧ Irrational (r/(1+r))
  have hden : 0 < 1+r := by linarith
  refine ⟨div_pos hr hden, (div_lt_iff₀ hden).2 (by linarith), ?_⟩
  have he : r/(1+r) = 1-(1+r)⁻¹ := by field_simp
  rw [he]
  simpa using ((hir.natCast_add 1).inv.natCast_sub 1)

private theorem maps_directive {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hi : Irrational a) (k : Nat) :
    MapsPrefixes (standardMorphism (directiveExponent a k)) (tailSlope a (k+1)) (tailSlope a k) := by
  obtain ⟨hb,hb',hib⟩ := tail_bounds ha ha' hi k
  have hm := maps_standard (directiveExponent a k) hb (by linarith : tailSlope a (k+1) < 1) hib
  let r := remainder a (k+1)
  have hr := (remainder_bounds ha ha' hi (k+1)).1
  have hden : 0 < 1+r := by dsimp [r]; linarith
  have hc : 1-tailSlope a (k+1) = (1+r)⁻¹ := by
    change 1-r/(1+r) = _
    field_simp
  rw [hc] at hm
  have he (d : Nat) : (1+r)⁻¹/(1+d*(1+r)⁻¹) = (1+r+d)⁻¹ := by
    field_simp
  rw [he] at hm
  have hrec := reciprocal_remainder ha ha' hi k
  change (remainder a k)⁻¹ = (partialQuotient a k : ℝ) + r at hrec
  have hak := (remainder_bounds ha ha' hi k).1
  convert hm using 1
  cases k with
  | zero =>
    have hq := partialQuotient_pos hi 0
    simp only [directiveExponent, tailSlope, remainder, Nat.cast_sub (show 1 ≤ partialQuotient a 0 by omega),
      Nat.cast_one] at *
    rw [show 1+r+((partialQuotient a 0:ℝ)-1) = a⁻¹ by linarith, inv_inv]
  | succ k =>
    simp only [directiveExponent, tailSlope]
    rw [show 1+r+(partialQuotient a (k+1):ℝ) = 1+(remainder a (k+1))⁻¹ by linarith]
    field_simp
    exact Or.inl (add_comm _ _)

private noncomputable def directiveImage (a : ℝ) : Nat → List Bool → List Bool
  | 0, w => w
  | n+1, w => directiveImage a n (standardMorphism (directiveExponent a n) w)

private theorem image_append (a : ℝ) (n : Nat) (v w : List Bool) :
    directiveImage a n (v++w) = directiveImage a n v ++ directiveImage a n w := by
  induction n generalizing v w with
  | zero => rfl
  | succ n ih => rw [directiveImage, morphism_append, ih]; rfl

private theorem image_nil (a : ℝ) (n : Nat) : directiveImage a n [] = [] := by
  have h := congrArg List.length (image_append a n [] [])
  simp only [List.append_nil, List.length_append] at h
  exact List.length_eq_zero_iff.1 (by omega)

private theorem image_zeros (a : ℝ) (n d : Nat) : directiveImage a n (List.replicate d false) =
    (List.replicate d (directiveImage a n [false])).flatten := by
  induction d with
  | zero => exact image_nil a n
  | succ d ih =>
    rw [List.replicate_succ, show false :: List.replicate d false = [false] ++ List.replicate d false by rfl,
      image_append, ih, List.replicate_succ, List.flatten_cons]

/-- Standard words of the continued fraction, indexed starting at s₀.
The preceding seed s₋₁ is [true]. -/
noncomputable def continuedWord (a : ℝ) (n : Nat) := directiveImage a n [false]

theorem continuedWord_zero (a : ℝ) : continuedWord a 0 = [false] := rfl

theorem continuedWord_one (a : ℝ) :
    continuedWord a 1 = List.replicate (partialQuotient a 0 - 1) false ++ [true] :=
  morphism_zero _

/-- The source recurrence s_(n+2) = s_(n+1)^a_(n+2) s_n. -/
theorem continuedWord_step (a : ℝ) (n : Nat) : continuedWord a (n+2) =
    (List.replicate (partialQuotient a (n+1)) (continuedWord a (n+1))).flatten ++ continuedWord a n := by
  change directiveImage a (n+1) (standardMorphism (partialQuotient a (n+1)) [false]) = _
  rw [morphism_zero, image_append, image_zeros]
  simp only [directiveImage, morphism_one, continuedWord]

private theorem maps_image {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hi : Irrational a) (n : Nat) :
    MapsPrefixes (directiveImage a n) (tailSlope a n) a := by
  induction n with
  | zero => exact fun k => ⟨k,rfl⟩
  | succ n ih =>
    intro j
    obtain ⟨k,hk⟩ := maps_directive ha ha' hi n j
    obtain ⟨l,hl⟩ := ih k
    exact ⟨l, by rw [directiveImage, hk, hl]⟩

/-- All positive stages are prefixes, including the case a₁ = 1, where
the initial seed s₀ is not necessarily a prefix of s₁. -/
theorem continuedWord_succ_prefix {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hi : Irrational a) (n : Nat) :
    continuedWord a (n+1) = factorList (characteristicWord a) 0 (continuedWord a (n+1)).length := by
  obtain ⟨hb,hb',_⟩ := tail_bounds ha ha' hi n
  let b := tailSlope a (n+1)
  have h₁ : ⌊b⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hb.le, by dsimp [b]; linarith⟩
  have h₂ : ⌊2*b⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨by dsimp [b]; positivity, by dsimp [b]; linarith⟩
  have first : factorList (characteristicWord b) 0 1 = [false] := by
    simp [factorList, characteristic_letter_floor_eq, h₁,h₂]
  obtain ⟨k,hk⟩ := maps_image ha ha' hi (n+1) 1
  change directiveImage a (n+1) (factorList (characteristicWord b) 0 1) = _ at hk
  rw [first] at hk
  change continuedWord a (n+1) = _ at hk
  have hlen := congrArg List.length hk
  simp only [factorList, List.length_ofFn] at hlen
  rwa [hlen]

private theorem length_replicate_flatten (d : Nat) (w : List Bool) :
    (List.replicate d w).flatten.length = d*w.length := by
  induction d with
  | zero => simp
  | succ d ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem continuedWord_length_pos (a : ℝ) : ∀ k, 0 < (continuedWord a k).length
  | 0 => Nat.zero_lt_one
  | 1 => by simp [continuedWord_one]
  | k+2 => by rw [continuedWord_step, List.length_append]; exact Nat.add_pos_right _ (continuedWord_length_pos a k)

theorem continuedWord_length_grows {a : ℝ} (hi : Irrational a) (n : Nat) :
    n+1 ≤ (continuedWord a (n+1)).length := by
  induction n with
  | zero => exact continuedWord_length_pos a 1
  | succ n ih =>
    rw [continuedWord_step, List.length_append, length_replicate_flatten]
    have hq := partialQuotient_pos hi (n+1)
    have h := Nat.le_mul_of_pos_left (continuedWord a (n+1)).length hq
    have hp := continuedWord_length_pos a n
    omega

/-- Convergence in proirrationaln1: for every length m, every stage after
m agrees with the characteristic mechanical word on its first m letters. -/
theorem continuedWord_tendsto_characteristic {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hi : Irrational a) (m : Nat) :
    ∀ᶠ n in atTop, (continuedWord a n).take m = factorList (characteristicWord a) 0 m := by
  filter_upwards [eventually_ge_atTop (m+1)] with n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hl := continuedWord_length_grows hi k
  have hp := factorList_prefix (characteristicWord a) (show m ≤ (continuedWord a (k+1)).length by omega)
  obtain ⟨v,hv⟩ := hp
  conv_lhs => rw [continuedWord_succ_prefix ha ha' hi k, ← hv]
  simpa only [factorList, List.length_ofFn] using (List.take_left (l₁ := factorList (characteristicWord a) 0 m) (l₂ := v))

end Thesis.SturmianDensity
