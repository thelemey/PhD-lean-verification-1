import Thesis.PalindromicMorphisms

namespace Thesis.PalindromeFactors

variable {α : Type*} [DecidableEq α]

private def innerPalImage (a : α) (v : List α) : List α :=
  (leftPalMorphism a v).tail

private theorem centeredPalImage_head (a : α) (v : List α) :
    (centeredPalImage a v).head? = some a := by
  simp [centeredPalImage, leftPalMorphism_append_letter]

private theorem centeredPalImage_nil (a : α) : centeredPalImage a [] = [a] := rfl

private theorem centeredPalImage_eq_wrap (a : α) {v : List α} (h : v ≠ []) :
    centeredPalImage a v = a :: (innerPalImage a v ++ [a]) := by
  cases v with
  | nil => exact False.elim (h rfl)
  | cons b v => by_cases he : b = a <;>
      simp [centeredPalImage, innerPalImage, leftPalMorphism, he]

private theorem innerPalImage_head (a : α) {v : List α} (h₀ : v ≠ []) (h₁ : v.head? ≠ some a) :
    (innerPalImage a v).head? = v.head? := by
  cases v with
  | nil => exact False.elim (h₀ rfl)
  | cons b v =>
    have h : b ≠ a := fun he => h₁ (by simp [he])
    simp [innerPalImage, leftPalMorphism, h]

private theorem centeredPalImage_pal (a : α) {v w : List α} (h : PalindromicFactor w v) :
    PalindromicFactor (centeredPalImage a w) (centeredPalImage a v) := by
  refine ⟨fun he => by
    have hh := congrArg List.head? he
    simp [centeredPalImage_head] at hh, centeredPalImage_infix a h.2.1, ?_⟩
  rw [reverse_centeredPalImage, h.2.2]

private theorem innerPalImage_pal (a : α) {v w : List α} (h : PalindromicFactor w v)
    (hhead : v.head? ≠ some a) :
    PalindromicFactor (centeredPalImage a w) (innerPalImage a v) := by
  have hcenter := centeredPalImage_pal a h
  have hpre : innerPalImage a v <:+: centeredPalImage a v :=
    ⟨[a], [a], by simp [centeredPalImage_eq_wrap a h.1]⟩
  refine ⟨fun he => ?_, hpre.trans hcenter.2.1, ?_⟩
  · have hh := innerPalImage_head a h.1 hhead
    rw [he, List.head?_nil] at hh
    exact h.1 (List.head?_eq_none_iff.1 hh.symm)
  · have hr := hcenter.2.2
    rw [centeredPalImage_eq_wrap a h.1, List.reverse_cons, List.reverse_append] at hr
    have hc : a :: ((innerPalImage a v).reverse ++ [a]) =
        a :: (innerPalImage a v ++ [a]) := by simpa using hr
    exact List.append_cancel_right (List.cons.inj hc).2

/-- The episturmian letter morphism preserves richness. The centered
images contribute one palindrome for every original palindrome. Those
beginning with a letter other than a also give the distinct inner images. -/
theorem rich_centeredPalImage (a : α) {w : List α} (hw : Rich w) :
    Rich (centeredPalImage a w) := by
  obtain ⟨ps, hp, hlen⟩ := hw
  obtain ⟨qs, hq⟩ := exists_enumeration (centeredPalImage a w)
  let chosen := ps.filter fun v => decide (v.head? ≠ some a)
  let centered := ps.map (centeredPalImage a)
  let inner := chosen.map (innerPalImage a)
  have hchosen (v : List α) (hv : v ∈ chosen) :
      PalindromicFactor w v ∧ v.head? ≠ some a := by
    obtain ⟨hm, ht⟩ := List.mem_filter.1 hv
    exact ⟨(hp.2 v).1 hm, of_decide_eq_true ht⟩
  have hcentered : centered.Nodup := hp.1.map (centeredPalImage_injective a)
  have hinner : inner.Nodup := by
    have hn : chosen.Nodup := hp.1.filter _
    apply (List.nodup_map_iff_inj_on hn).2
    intro v hv z hz he
    apply centeredPalImage_injective a
    rw [centeredPalImage_eq_wrap a (hchosen v hv).1.1,
      centeredPalImage_eq_wrap a (hchosen z hz).1.1, he]
  have hdisjoint : List.Disjoint centered inner := by
    intro v hv hi
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 hv
    obtain ⟨z, hz, he⟩ := List.mem_map.1 hi
    have hh := congrArg List.head? he
    rw [centeredPalImage_head, innerPalImage_head a (hchosen z hz).1.1 (hchosen z hz).2] at hh
    exact (hchosen z hz).2 hh
  have hsingle : [a] ∉ centered ++ inner := by
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨u, hu, hU⟩ := List.mem_map.1 hm
      have he := centeredPalImage_injective a (hU.trans (centeredPalImage_nil a).symm)
      exact ((hp.2 u).1 hu).1 he
    · obtain ⟨v, hv, he⟩ := List.mem_map.1 hm
      have hh := congrArg List.head? he
      rw [innerPalImage_head a (hchosen v hv).1.1 (hchosen v hv).2] at hh
      exact (hchosen v hv).2 hh
  have hpal (v : List α) (hv : v ∈ [a] :: (centered ++ inner)) :
      PalindromicFactor (centeredPalImage a w) v := by
    rcases List.mem_cons.1 hv with rfl | hm
    · refine ⟨by simp, ⟨[], rightPalMorphism a w, ?_⟩, by simp⟩
      simp [centeredPalImage, leftPalMorphism_append_letter]
    · rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hm
        exact centeredPalImage_pal a ((hp.2 u).1 hu)
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hm
        exact innerPalImage_pal a (hchosen u hu).1 (hchosen u hu).2
  have hbound := FiniteList.nodup_length_le_of_subset
    (List.nodup_cons.2 ⟨hsingle, hcentered.append hinner hdisjoint⟩)
    (fun v hv => (hq.2 v).2 (hpal v hv))
  have hcount := rich_nondistinguished_palindrome_count a w hp hlen
  have hupper := palindromicFactor_count_le_length _ hq
  refine ⟨qs, hq, Nat.le_antisymm hupper ?_⟩
  simp only [List.length_cons, List.length_append, centered, inner, chosen, List.length_map,
    hlen, hcount] at hbound
  simp only [centeredPalImage, List.length_append, length_leftPalMorphism, List.length_cons,
    List.length_nil]
  omega

theorem rich_leftPalMorphism (a : α) {w : List α} (hw : Rich w) :
    Rich (leftPalMorphism a w) :=
  rich_of_infix (rich_centeredPalImage a hw) (List.prefix_append _ _).isInfix

end Thesis.PalindromeFactors
