import Mathlib.Data.Nat.Find
import Mathlib.Data.List.Basic

namespace Thesis.PalindromicClosure

variable {α : Type*}

private def PalExtension (w : List α) (n : Nat) : Prop :=
  ∃ v : List α, v.length = n ∧ w <+: v ∧ v.reverse = v

private theorem exists_palExtension (w : List α) : ∃ n, PalExtension w n :=
  ⟨(w ++ w.reverse).length, w ++ w.reverse, rfl, List.prefix_append _ _, by simp⟩

/-- The shortest palindrome with a given word as prefix. -/
noncomputable def close (w : List α) : List α := by
  classical
  exact Classical.choose (Nat.find_spec (exists_palExtension w))

private theorem close_spec (w : List α) :
    (close w).length = (by classical exact Nat.find (exists_palExtension w)) ∧
      w <+: close w ∧ (close w).reverse = close w := by
  classical
  exact Classical.choose_spec (Nat.find_spec (exists_palExtension w))

theorem prefix_close (w : List α) : w <+: close w :=
  (close_spec w).2.1

theorem reverse_close (w : List α) : (close w).reverse = close w :=
  (close_spec w).2.2

theorem close_length_le {w v : List α} (hp : w <+: v) (hv : v.reverse = v) :
    (close w).length ≤ v.length := by
  classical
  rw [(close_spec w).1]
  exact Nat.find_min' _ ⟨v, rfl, hp, hv⟩

private theorem extension_of_suffix {w s : List α} (hs : s <:+ w) (hp : s.reverse = s) :
    ∃ v : List α, w <+: v ∧ v.reverse = v ∧ v.length = 2 * w.length - s.length := by
  obtain ⟨l, rfl⟩ := hs
  refine ⟨l ++ s ++ l.reverse, List.prefix_append _ _, ?_, ?_⟩
  · simp [hp, List.append_assoc]
  · simp only [List.length_append, List.length_reverse]
    omega

private theorem suffix_of_short_extension {w v : List α}
    (hw : w <+: v) (hv : v.reverse = v) (hl : v.length ≤ 2 * w.length) :
    ∃ s : List α, s <:+ w ∧ s.reverse = s ∧ s.length = 2 * w.length - v.length := by
  obtain ⟨r, rfl⟩ := hw
  have hrl : r.reverse.length ≤ w.length := by simp only [List.length_append] at hl; simpa using
    (show r.length ≤ w.length by omega)
  have hrp : r.reverse <+: w ++ r := by
    have h := (List.suffix_append w r).reverse
    rwa [hv] at h
  obtain ⟨s, hs⟩ := List.prefix_of_prefix_length_le hrp (List.prefix_append w r) hrl
  refine ⟨s, ⟨r.reverse, hs⟩, ?_, ?_⟩
  · rw [← hs] at hv
    simp only [List.reverse_append, List.reverse_reverse, List.append_assoc] at hv
    exact List.append_cancel_right (List.append_cancel_left hv)
  · have h := congrArg List.length hs
    simp only [List.length_append, List.length_reverse] at h ⊢
    omega

/-- The closure length is twice the initial length minus the length of
the longest palindromic suffix, including the empty suffix if necessary. -/
theorem close_length_of_longest_suffix {w s : List α}
    (hs : s <:+ w) (hp : s.reverse = s)
    (hmax : ∀ v : List α, v <:+ w → v.reverse = v → v.length ≤ s.length) :
    (close w).length = 2 * w.length - s.length := by
  obtain ⟨v, hv, hvpal, he⟩ := extension_of_suffix hs hp
  have hle := close_length_le hv hvpal
  rw [he] at hle
  obtain ⟨q, hq, hqpal, hqLen⟩ :=
    suffix_of_short_extension (prefix_close w) (reverse_close w) (by omega)
  have hqle := hmax q hq hqpal
  omega

end Thesis.PalindromicClosure
