import Thesis.PalindromeFactors
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Equiv.Defs

namespace Thesis.PalindromeFactors

variable {α β : Type*}

/-- A bijective change of letters preserves the palindrome count. -/
theorem rich_rename (e : α ≃ β) {w : List α} (hw : Rich w) : Rich (w.map e) := by
  obtain ⟨ps, hp, hlen⟩ := hw
  have hl (v : List α) : (v.map e).map e.symm = v := by
    induction v <;> simp_all
  have hr (v : List β) : (v.map e.symm).map e = v := by
    induction v <;> simp_all
  have hinj : Function.Injective (List.map e) := fun v z h => by
    simpa only [hl] using congrArg (List.map e.symm) h
  refine ⟨ps.map (List.map e), ⟨hp.1.map hinj, ?_⟩, by simpa using hlen⟩
  intro v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
    obtain ⟨hne, ⟨l, r, he⟩, hpal⟩ := (hp.2 u).1 hu
    refine ⟨by simpa using hne, ⟨l.map e, r.map e, ?_⟩, ?_⟩
    · simpa only [List.map_append] using congrArg (List.map e) he
    · rw [← List.map_reverse, hpal]
  · rintro ⟨hne, ⟨l, r, he⟩, hpal⟩
    apply List.mem_map.2
    refine ⟨v.map e.symm, (hp.2 _).2 ⟨by simpa using hne, ⟨l.map e.symm, r.map e.symm, ?_⟩, ?_⟩,
      hr v⟩
    · simpa only [List.map_append, hl] using congrArg (List.map e.symm) he
    · rw [← List.map_reverse, hpal]

variable [DecidableEq α]

/-- The left episturmian morphism at a fixes a and sends b to ab
for every other letter b. -/
def leftPalMorphism (a : α) (w : List α) : List α :=
  w.flatMap (fun b => if b = a then [a] else [a, b])

/-- The right episturmian morphism uses the reversed letter images. -/
def rightPalMorphism (a : α) (w : List α) : List α :=
  w.flatMap (fun b => if b = a then [a] else [b, a])

theorem leftPalMorphism_append (a : α) (u v : List α) :
    leftPalMorphism a (u ++ v) = leftPalMorphism a u ++ leftPalMorphism a v := by
  simp [leftPalMorphism]

private theorem rightPalMorphism_append (a : α) (u v : List α) :
    rightPalMorphism a (u ++ v) = rightPalMorphism a u ++ rightPalMorphism a v := by
  simp [rightPalMorphism]

/-- Moving the final a through the left images produces the right images. -/
theorem leftPalMorphism_append_letter (a : α) (w : List α) :
    leftPalMorphism a w ++ [a] = a :: rightPalMorphism a w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    by_cases h : b = a
    · subst b
      simpa [leftPalMorphism, rightPalMorphism] using congrArg (List.cons a) ih
    · simpa [leftPalMorphism, rightPalMorphism, h] using congrArg (List.cons a ∘ List.cons b) ih

private theorem reverse_leftPalMorphism (a : α) (w : List α) :
    (leftPalMorphism a w).reverse = rightPalMorphism a w.reverse := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.reverse_cons, rightPalMorphism_append]
    rw [show leftPalMorphism a (b :: w) = leftPalMorphism a [b] ++ leftPalMorphism a w from
      leftPalMorphism_append a [b] w, List.reverse_append, ih]
    congr 1
    by_cases h : b = a <;> simp [leftPalMorphism, rightPalMorphism, h]

private theorem rightPalMorphism_head (a b : α) (w : List α) :
    (rightPalMorphism a (b :: w)).head? = some b := by
  by_cases h : b = a <;> simp [rightPalMorphism, h]

private theorem rightPalMorphism_injective (a : α) : Function.Injective (rightPalMorphism a) := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b v =>
      have he := congrArg List.head? h
      rw [rightPalMorphism_head] at he
      change none = some b at he
      contradiction
  | cons b u ih =>
    intro v h
    cases v with
    | nil =>
      have he := congrArg List.head? h
      rw [rightPalMorphism_head] at he
      change some b = none at he
      contradiction
    | cons c v =>
      have hbc : b = c := by
        have he := congrArg List.head? h
        simpa only [rightPalMorphism_head, Option.some.injEq] using he
      subst c
      congr 1
      apply ih
      exact List.append_cancel_left h

/-- The centered image that lifts a palindrome through the morphism. -/
def centeredPalImage (a : α) (v : List α) : List α :=
  leftPalMorphism a v ++ [a]

theorem centeredPalImage_injective (a : α) : Function.Injective (centeredPalImage a) := by
  intro v z h
  unfold centeredPalImage at h
  rw [leftPalMorphism_append_letter, leftPalMorphism_append_letter] at h
  exact rightPalMorphism_injective a (List.cons.inj h).2

theorem reverse_centeredPalImage (a : α) (v : List α) :
    (centeredPalImage a v).reverse = centeredPalImage a v.reverse := by
  unfold centeredPalImage
  rw [List.reverse_append, reverse_leftPalMorphism, leftPalMorphism_append_letter]
  rfl

theorem centeredPalImage_infix (a : α) {v w : List α} (h : v <:+: w) :
    centeredPalImage a v <:+: centeredPalImage a w := by
  obtain ⟨l, r, rfl⟩ := h
  refine ⟨leftPalMorphism a l, rightPalMorphism a r, ?_⟩
  simp only [centeredPalImage, leftPalMorphism_append, List.append_assoc]
  rw [leftPalMorphism_append_letter]
  rfl

theorem length_leftPalMorphism (a : α) (v : List α) :
    (leftPalMorphism a v).length = v.length + (v.filter fun b => decide (b ≠ a)).length := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    change (leftPalMorphism a ([b] ++ v)).length = _
    rw [leftPalMorphism_append, List.length_append, ih]
    by_cases h : b = a <;> simp [leftPalMorphism, h] <;> omega

end Thesis.PalindromeFactors
