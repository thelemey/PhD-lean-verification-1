import Thesis.FactorialWeyl
import Thesis.ThueMorseComplexity
import Thesis.WordPrefixLimits

namespace Thesis.FactorialWord

open WordPrefixLimits Filter

private theorem prefix_covers {b : Nat} (hb : 1 < b) (j : Nat) :
    j < (concatenation b (j + 1)).length :=
  (Nat.lt_succ_self j).trans_le (concatenation_length_ge hb _)

/-- The infinite sequence of digits in 0!, 1!, 2!, … in base b. -/
def infiniteDigits (b : Nat) (hb : 1 < b) : Nat → Nat :=
  prefixLimit (fun n => concatenation b (n + 1)) (prefix_covers hb)

theorem infiniteDigits_eq_getElem {b n j : Nat} (hb : 1 < b)
    (hj : j < (concatenation b n).length) :
    infiniteDigits b hb j = (concatenation b n)[j] := by
  cases n with
  | zero => simp [concatenation] at hj
  | succ n =>
    exact prefixLimit_eq_getElem _ (prefix_covers hb)
      (fun n => concatenation_prefix b (n + 1)) hj

/-- The n-th factorial begins immediately after the first n factorial blocks. -/
theorem infiniteDigits_factorial_block {b : Nat} (hb : 1 < b) (n : Nat) {j : Nat}
    (hj : j < ((digits b (factorial n)).reverse).length) :
    infiniteDigits b hb ((concatenation b n).length + j) =
      ((digits b (factorial n)).reverse)[j] := by
  have hi : (concatenation b n).length + j < (concatenation b (n + 1)).length := by
    rw [concatenation, List.length_append]
    exact Nat.add_lt_add_left hj _
  rw [infiniteDigits_eq_getElem hb hi]
  simp only [concatenation, List.getElem_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-- The count in lem:trail tends to infinity, as witnessed by the
prime-valuation threshold. -/
theorem factorial_trailingZeroCount_tendsto_atTop {b : Nat} (hb : 1 < b) :
    Tendsto (fun n => trailingZeroCount b (factorial n)) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (b * k)] with n hn
  exact (le_trailingZeroCount_iff_dvd hb (factorial_pos n) k).2
    (pow_dvd_factorial (zero_lt_one.trans hb) k n hn)

/-- The same word as an element of the product of the base-b alphabet. -/
def infiniteWord (b : Nat) (hb : 1 < b) (j : Nat) : Fin b :=
  ⟨infiniteDigits b hb j, digit_of_concatenation hb (j + 1) _ (List.getElem_mem _)⟩

theorem factor_iff_infiniteDigits {b : Nat} (hb : 1 < b) (v : List Nat) :
    Factor b v ↔ ∃ i, v = List.ofFn (fun j : Fin v.length => infiniteDigits b hb (i + j.val)) := by
  unfold infiniteDigits
  rw [factor_prefixLimit_iff _ (prefix_covers hb)
    (fun n => concatenation_prefix b (n + 1)) v]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.trans (concatenation_prefix b n).isInfix⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩

theorem arithmeticFactor_iff_infiniteDigits {b : Nat} (hb : 1 < b) (v : List Nat) :
    ArithmeticFactor b v ↔ ∃ start step : Nat, 0 < step ∧
      ∀ i : Fin v.length, infiniteDigits b hb (start + step * i.val) = v[i] := by
  constructor
  · rintro ⟨n, start, step, hs, h⟩
    refine ⟨start, step, hs, fun i => ?_⟩
    have he := h i.val i.isLt
    have hi : start + step * i.val < (concatenation b n).length := by
      by_contra! hbad
      rw [List.getElem?_eq_none hbad] at he
      cases he
    simpa only [infiniteDigits_eq_getElem hb hi, List.getElem?_eq_getElem hi,
      Option.some.injEq] using he
  · rintro ⟨start, step, hs, h⟩
    let n := start + step * v.length + 1
    refine ⟨n, start, step, hs, fun i hi => ?_⟩
    have hmul : step * i ≤ step * v.length := Nat.mul_le_mul_left _ hi.le
    have hbnd : start + step * i < (concatenation b n).length :=
      (show start + step * i < n by dsimp [n]; omega).trans_le (concatenation_length_ge hb n)
    rw [List.getElem?_eq_getElem hbnd, ← infiniteDigits_eq_getElem hb hbnd,
      h ⟨i, hi⟩]
    rfl

/-- The length-k arithmetic factors of an infinite word over a finite alphabet. -/
noncomputable def arithmeticLanguage {A : Type*} [Fintype A] (w : Nat → A) (k : Nat) :
    Finset (Fin k → A) := by
  classical
  exact Finset.univ.filter fun u =>
    ∃ start step : Nat, 0 < step ∧ ∀ j : Fin k, w (start + step * j.val) = u j

theorem factorLanguage_subset_arithmeticLanguage {A : Type*} [Fintype A] (w : Nat → A)
    (k : Nat) : ThueMorse.factorLanguage w k ⊆ arithmeticLanguage w k := by
  classical
  intro u hu
  obtain ⟨i, rfl⟩ := (ThueMorse.mem_factorLanguage _ _ _).1 hu
  simp only [arithmeticLanguage, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, 1, by decide, fun j => by simp [ThueMorse.window]⟩

theorem factorial_factorLanguage_univ {b : Nat} (hb : 1 < b) (k : Nat) :
    ThueMorse.factorLanguage (infiniteWord b hb) k = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro u
  let v := List.ofFn fun j : Fin k => (u j).val
  have hv : ∀ d ∈ v, d < b := by
    intro d hd
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hd
    exact (u j).isLt
  have hfactor := (factor_iff_digits hb (factorial_leading_prefixes hb) v).2 hv
  obtain ⟨i, hi⟩ := (factor_iff_infiniteDigits hb v).1 hfactor
  apply (ThueMorse.mem_factorLanguage _ _ _).2
  refine ⟨i, funext fun j => Fin.ext ?_⟩
  have hlen : v.length = k := by simp [v]
  have hjv : j.val < v.length := by rw [hlen]; exact j.isLt
  have he := congrArg (fun l : List Nat => l[j.val]?) hi
  change v[j.val]? = (List.ofFn (fun t : Fin v.length => infiniteDigits b hb (i + t.val)))[j.val]? at he
  have hleft : v[j.val]? = some (u j).val := by
    simp [v, List.getElem?_ofFn, j.isLt]
  rw [hleft, List.getElem?_ofFn, dif_pos hjv] at he
  exact (Option.some.inj he).symm

theorem factorial_arithmeticLanguage_univ {b : Nat} (hb : 1 < b) (k : Nat) :
    arithmeticLanguage (infiniteWord b hb) k = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro u
  apply factorLanguage_subset_arithmeticLanguage
  rw [factorial_factorLanguage_univ hb]
  exact Finset.mem_univ _

/-- The two equalities in mainthm01 as cardinalities of factor languages
of the actual infinite concatenation. The arithmetic equality follows
from containment of factors as progressions of step one. -/
theorem infiniteWord_full_complexities {b : Nat} (hb : 1 < b) (k : Nat) :
    ThueMorse.complexity (infiniteWord b hb) k = b ^ k ∧
      (arithmeticLanguage (infiniteWord b hb) k).card = b ^ k := by
  simp [ThueMorse.complexity, factorial_factorLanguage_univ hb,
    factorial_arithmeticLanguage_univ hb, Fintype.card_fun]

end Thesis.FactorialWord
