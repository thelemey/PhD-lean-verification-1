import Mathlib.Data.List.OfFn

namespace Thesis.WordPrefixLimits

variable {α : Type*}

/-- The limit of a nested sequence of finite words, read at position j
from a word that already contains that position. -/
def prefixLimit (s : Nat → List α) (hcover : ∀ j, j < (s j).length) (j : Nat) : α :=
  (s j)[j]'(hcover j)

theorem prefix_of_le (s : Nat → List α) (hstep : ∀ n, s n <+: s (n + 1))
    {i j : Nat} (h : i ≤ j) : s i <+: s j := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | step _ ih => exact ih.trans (hstep _)

theorem prefixLimit_eq_getElem (s : Nat → List α) (hcover : ∀ j, j < (s j).length)
    (hstep : ∀ n, s n <+: s (n + 1)) {n j : Nat} (hj : j < (s n).length) :
    prefixLimit s hcover j = (s n)[j] := by
  unfold prefixLimit
  rcases Nat.le_total j n with h | h
  · exact (prefix_of_le s hstep h).getElem (hcover j)
  · exact ((prefix_of_le s hstep h).getElem hj).symm

/-- The finite factors of a prefix limit are precisely the infixes of
some finite approximant. -/
theorem factor_prefixLimit_iff (s : Nat → List α) (hcover : ∀ j, j < (s j).length)
    (hstep : ∀ n, s n <+: s (n + 1)) (v : List α) :
    (∃ i : Nat, v = List.ofFn (fun j : Fin v.length => prefixLimit s hcover (i + j.val))) ↔
      ∃ n : Nat, v <:+: s n := by
  constructor
  · rintro ⟨i, hi⟩
    let n := i + v.length
    let q := ((s n).drop i).take v.length
    have hn : i + v.length < (s n).length := hcover n
    have mq : q.length = v.length := by
      simp only [q, List.length_take, List.length_drop]
      exact min_eq_left (by omega)
    have he : v = q := by
      apply List.ext_getElem mq.symm
      intro j hj hq
      have hidx : i + j < (s n).length := by omega
      have hV : v[j] = prefixLimit s hcover (i + j) := by
        have hElem := congrArg (fun w : List α => w[j]?) hi
        have hj' : j < (List.ofFn (fun t : Fin v.length => prefixLimit s hcover (i + t.val))).length := by
          simpa using hj
        simpa only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
          List.getElem_ofFn, Option.some.injEq] using hElem
      rw [hV, prefixLimit_eq_getElem s hcover hstep hidx]
      simp [q]
    refine ⟨n, ?_⟩
    rw [he]
    exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
  · rintro ⟨n, l, r, hl⟩
    refine ⟨l.length, ?_⟩
    apply List.ext_getElem (by simp)
    intro j hj _
    simp only [List.getElem_ofFn]
    have hlen : l.length + j < (s n).length := by rw [← hl]; simp only [List.length_append]; omega
    have he := prefixLimit_eq_getElem s hcover hstep hlen
    have hlen' : l.length + j < (l ++ v ++ r).length := by simp only [List.length_append]; omega
    have hElem : (l ++ v ++ r)[l.length + j] = (s n)[l.length + j] := by
      simpa only [List.getElem?_eq_getElem hlen', List.getElem?_eq_getElem hlen, Option.some.injEq] using
        congrArg (fun w : List α => w[l.length + j]?) hl
    rw [he, ← hElem, List.getElem_append_left (by simp only [List.length_append]; omega),
      List.getElem_append_right (by omega)]
    simp

end Thesis.WordPrefixLimits
