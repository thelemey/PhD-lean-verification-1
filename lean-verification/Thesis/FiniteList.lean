import Std.Tactic

namespace Thesis.FiniteList

theorem nodup_length_le_of_subset [DecidableEq β] {xs ys : List β}
    (hnd : xs.Nodup) (hs : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    have ha : a ∈ ys := hs a (by simp)
    have htail : ∀ x ∈ xs, x ∈ ys.erase a := by
      intro x hx
      have hne : x ≠ a := fun he => hna (he ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hs x (List.mem_cons_of_mem _ hx))
    have hle := ih hnd' htail
    rw [List.length_erase_of_mem ha] at hle
    have hp := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

end Thesis.FiniteList
