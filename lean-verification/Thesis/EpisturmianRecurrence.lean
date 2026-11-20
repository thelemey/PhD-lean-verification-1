import Thesis.EpisturmianPrefixes

namespace Thesis.Episturmian

open PalindromicClosure WordPrefixLimits

variable {α : Type*}

private theorem long_suffix_shape {w v : List α} {a : α} (hw : w.reverse = w)
    (hvs : v <:+ w ++ [a]) (hv : v.reverse = v) (hlen : 2 ≤ v.length) :
    ∃ q : List α, v = a :: (q ++ [a]) ∧ q.reverse = q ∧ q ++ [a] <+: w := by
  have hpre := hvs.reverse
  rw [hv, List.reverse_append, hw] at hpre
  have hpre' : v <+: a :: w := by simpa using hpre
  cases v with
  | nil => simp at hlen
  | cons b tail =>
    obtain ⟨r, hr⟩ := hpre'
    have ha : b = a := (List.cons.inj hr).1
    subst b
    have ht : tail <+: w := ⟨r, (List.cons.inj hr).2⟩
    have hfirst : [a] <+: a :: tail := ⟨tail, rfl⟩
    have hlast : [a] <:+ a :: tail := by
      have hs := hfirst.reverse
      simpa [hv] using hs
    obtain ⟨p, hp⟩ := hlast
    cases p with
    | nil =>
      have he : tail = [] := (List.cons.inj hp).2.symm
      simp [he] at hlen
    | cons c q =>
      have hq : q ++ [a] = tail := (List.cons.inj hp).2
      subst tail
      refine ⟨q, rfl, ?_, ht⟩
      rw [List.reverse_cons, List.reverse_append] at hv
      have he : a :: (q.reverse ++ [a]) = a :: (q ++ [a]) := by simpa using hv
      exact List.append_cancel_right (List.cons.inj he).2

private theorem long_suffix_from_previous (directive : Nat → α) (n : Nat) {v : List α}
    (hvs : v <:+ stage directive n ++ [directive n]) (hv : v.reverse = v) (hlen : 2 ≤ v.length) :
    ∃ i < n, directive i = directive n ∧ v.length = (stage directive i).length + 2 := by
  obtain ⟨q, rfl, hpal, hp⟩ := long_suffix_shape (stage_reverse directive n) hvs hv hlen
  obtain ⟨i, hi, rfl⟩ := pal_prefix_stage directive n
    ((List.prefix_append _ _).trans hp) hpal
  have hlt : i < n := by
    have hh := hp.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at hh
    by_cases he : i = n
    · subst i
      omega
    · exact lt_of_le_of_ne hi he
  have hdir : stage directive i ++ [directive i] <+: stage directive n :=
    (stage_with_next_prefix directive i).trans
      (prefix_of_le (stage directive) (stage_prefix_step directive) (Nat.succ_le_of_lt hlt))
  have he := List.prefix_of_prefix_length_le hdir hp (by simp)
  have he' := prefix_eq_of_length_eq he (by simp)
  refine ⟨i, hlt, ?_, by simp⟩
  exact (List.cons.inj (List.append_cancel_left he')).1

/-- The first occurrence of a directive letter makes its singleton
the longest palindromic suffix. -/
theorem stage_length_of_new_letter (directive : Nat → α) (n : Nat)
    (hnew : ∀ i < n, directive i ≠ directive n) :
    (stage directive (n + 1)).length = 2 * (stage directive n).length + 1 := by
  have hh := close_length_of_longest_suffix
    (List.suffix_append (stage directive n) [directive n]) (by simp) ?_
  · change (close (stage directive n ++ [directive n])).length = _
    rw [hh]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro v hvs hv
    by_cases hlen : 2 ≤ v.length
    · obtain ⟨i, hi, he, _⟩ := long_suffix_from_previous directive n hvs hv hlen
      exact False.elim (hnew i hi he)
    · simpa using (show v.length ≤ 1 by omega)

/-- At a repeated directive letter, remove the length of the palindrome
stage before its latest occurrence from twice the current length. -/
theorem stage_length_of_previous_letter (directive : Nat → α) {j n : Nat} (hj : j < n)
    (he : directive j = directive n)
    (hlast : ∀ i, j < i → i < n → directive i ≠ directive n) :
    (stage directive (n + 1)).length =
      2 * (stage directive n).length - (stage directive j).length := by
  let p := stage directive j
  let w := stage directive n
  let a := directive n
  let s := a :: (p ++ [a])
  have hpre : p ++ [a] <+: w := by
    dsimp only [p, w, a]
    rw [← he]
    exact (stage_with_next_prefix directive j).trans
      (prefix_of_le (stage directive) (stage_prefix_step directive) (Nat.succ_le_of_lt hj))
  have hsuf : a :: p <:+ w := by
    have hh := hpre.reverse
    simpa [List.reverse_append, stage_reverse, p, w] using hh
  have hs : s <:+ w ++ [a] := by
    obtain ⟨l, hl⟩ := hsuf
    refine ⟨l, ?_⟩
    dsimp only [s]
    change l ++ ((a :: p) ++ [a]) = w ++ [a]
    rw [← List.append_assoc, hl]
  have hpal : s.reverse = s := by
    simp [s, p, List.reverse_cons, List.reverse_append, stage_reverse]
  have hmax (v : List α) (hv : v <:+ w ++ [a]) (hvp : v.reverse = v) : v.length ≤ s.length := by
    by_cases hlen : 2 ≤ v.length
    · obtain ⟨i, hi, hsame, hsize⟩ := long_suffix_from_previous directive n hv hvp hlen
      have hij : i ≤ j := by
        by_cases h : j < i
        · exact False.elim (hlast i h hi hsame)
        · omega
      have hm := (stage_length_strictMono directive).monotone hij
      simp only [s, p, List.length_append, List.length_cons, List.length_nil]
      omega
    · simp only [s, List.length_append, List.length_cons, List.length_nil]
      omega
  have hh := close_length_of_longest_suffix hs hpal hmax
  change (close (w ++ [a])).length = 2 * w.length - p.length
  rw [hh]
  simp only [s, List.length_append, List.length_cons, List.length_nil]
  omega

end Thesis.Episturmian
