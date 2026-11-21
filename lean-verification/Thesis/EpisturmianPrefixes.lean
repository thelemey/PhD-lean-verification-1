import Thesis.PalindromicClosure
import Thesis.WordPrefixLimits
import Thesis.Palindrome

namespace Thesis.Episturmian

open PalindromicClosure WordPrefixLimits

variable {α : Type*}

/-- Successive palindromic closures along the directive word. -/
noncomputable def stage (directive : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => close (stage directive n ++ [directive n])

theorem stage_with_next_prefix (directive : Nat → α) (n : Nat) :
    stage directive n ++ [directive n] <+: stage directive (n + 1) :=
  prefix_close _

theorem stage_prefix_step (directive : Nat → α) (n : Nat) :
    stage directive n <+: stage directive (n + 1) :=
  (List.prefix_append _ _).trans (stage_with_next_prefix directive n)

theorem stage_reverse (directive : Nat → α) : ∀ n, (stage directive n).reverse = stage directive n
  | 0 => rfl
  | _ + 1 => reverse_close _

theorem stage_length_strictMono (directive : Nat → α) :
    StrictMono (fun n => (stage directive n).length) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := (stage_with_next_prefix directive n).length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at h
  omega

theorem stage_length_ge (directive : Nat → α) (n : Nat) : n ≤ (stage directive n).length := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := stage_length_strictMono directive (Nat.lt_succ_self n)
    change (stage directive n).length < (stage directive (n + 1)).length at h
    omega

private theorem stage_cover (directive : Nat → α) (n : Nat) :
    n < (stage directive (n + 1)).length :=
  (Nat.lt_succ_self n).trans_le (stage_length_ge directive (n + 1))

/-- The standard episturmian word with this directive. -/
noncomputable def word (directive : Nat → α) : Nat → α :=
  prefixLimit (fun n => stage directive (n + 1)) (stage_cover directive)

theorem word_at_stage_length (directive : Nat → α) (n : Nat) :
    word directive (stage directive n).length = directive n := by
  have hpre := stage_with_next_prefix directive n
  have hidx : (stage directive n).length < (stage directive n ++ [directive n]).length := by simp
  have hread := prefixLimit_eq_getElem (fun j => stage directive (j + 1)) (stage_cover directive)
    (fun j => stage_prefix_step directive (j + 1)) (hidx.trans_le hpre.length_le)
  change word directive (stage directive n).length = _ at hread
  rw [hread, ← hpre.getElem hidx]
  simp [List.getElem_append_right (le_refl _)]

theorem prefix_eq_of_length_eq {u v : List α} (h : u <+: v) (hlen : u.length = v.length) :
    u = v := by
  obtain ⟨r, rfl⟩ := h
  simp only [List.length_append] at hlen
  have hr : r = [] := List.length_eq_zero_iff.1 (by omega)
  simp [hr]

/-- A palindromic prefix of a closure stage is one of the earlier stages.
A prefix strictly between two stages would contradict shortest closure. -/
theorem pal_prefix_stage (directive : Nat → α) (n : Nat) {v : List α}
    (hv : v <+: stage directive n) (hpal : v.reverse = v) :
    ∃ i ≤ n, v = stage directive i := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, prefix_eq_of_length_eq hv ?_⟩
    have h := hv.length_le
    simp [stage] at h ⊢
    exact h
  | succ n ih =>
    by_cases hlen : v.length ≤ (stage directive n).length
    · obtain ⟨i, hi, he⟩ := ih
        (List.prefix_of_prefix_length_le hv (stage_prefix_step directive n) hlen)
      exact ⟨i, hi.trans (Nat.le_succ n), he⟩
    · have hnext := stage_with_next_prefix directive n
      have hmin : (stage directive (n + 1)).length ≤ v.length :=
        close_length_le (List.prefix_of_prefix_length_le hnext hv (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)) hpal
      exact ⟨n + 1, le_rfl, prefix_eq_of_length_eq hv (le_antisymm hv.length_le hmin)⟩

private theorem palindrome_ofFn_iff (w : Nat → α) (k : Nat) :
    (List.ofFn (fun i : Fin k => w i.val)).reverse = List.ofFn (fun i : Fin k => w i.val) ↔
      PalPrefix w k := by
  constructor
  · intro h i hi
    have he := congrArg (fun v : List α => v[i]?) h
    have h₀ : i < (List.ofFn (fun i : Fin k => w i.val)).length := by simpa using hi
    have h₁ : i < (List.ofFn (fun i : Fin k => w i.val)).reverse.length := by simpa using hi
    have hh : w (k - 1 - i) = w i := by
      simpa only [List.getElem?_eq_getElem h₀, List.getElem?_eq_getElem h₁,
        List.getElem_reverse, List.length_ofFn, List.getElem_ofFn, Option.some.injEq] using he
    exact hh.symm
  · intro h
    apply List.ext_getElem (by simp)
    intro i hi _
    have hi' : i < k := by simpa using hi
    simpa only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn] using (h i hi').symm

private theorem word_prefix_eq_take (directive : Nat → α) {k n : Nat}
    (hk : k ≤ (stage directive (n + 1)).length) :
    List.ofFn (fun i : Fin k => word directive i.val) = (stage directive (n + 1)).take k := by
  apply List.ext_getElem (by simpa only [List.length_ofFn, List.length_take] using (min_eq_left hk).symm)
  intro i hi htake
  have hi' : i < k := by simpa using hi
  have h : i < (stage directive (n + 1)).length := hi'.trans_le hk
  simp only [List.getElem_ofFn, List.getElem_take]
  exact prefixLimit_eq_getElem (fun j => stage directive (j + 1)) (stage_cover directive)
    (fun j => stage_prefix_step directive (j + 1)) h

/-- The stages give exactly all palindrome-prefix lengths of the
standard episturmian word, including the zero length. -/
theorem palPrefix_word_iff (directive : Nat → α) (k : Nat) :
    PalPrefix (word directive) k ↔ ∃ n, (stage directive n).length = k := by
  rw [← palindrome_ofFn_iff]
  constructor
  · intro h
    let v := List.ofFn (fun i : Fin k => word directive i.val)
    have htake : v = (stage directive (k + 1)).take k :=
      word_prefix_eq_take directive (stage_cover directive k).le
    have hp : v <+: stage directive (k + 1) := by
      rw [htake]
      exact List.take_prefix _ _
    obtain ⟨n, _, he⟩ := pal_prefix_stage directive (k + 1) hp h
    refine ⟨n, ?_⟩
    rw [← he]
    simp [v]
  · rintro ⟨n, hn⟩
    have hp := stage_prefix_step directive n
    have hlen : k ≤ (stage directive (n + 1)).length := hn.symm.le.trans hp.length_le
    have ht : (stage directive (n + 1)).take k = stage directive n := by
      apply prefix_eq_of_length_eq
      · exact List.prefix_of_prefix_length_le (List.take_prefix _ _) hp (by simp [List.length_take, hn, hlen])
      · simp [List.length_take, hlen, hn]
    rw [word_prefix_eq_take directive hlen, ht, stage_reverse]

end Thesis.Episturmian
