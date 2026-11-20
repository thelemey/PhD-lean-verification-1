import Thesis.FiniteList

namespace Thesis.PalindromeFactors

/-- The morphism sending each letter to a separator followed by that letter. -/
def interleave : List α → List (Option α)
  | [] => []
  | a :: w => none :: some a :: interleave w

/-- The spelling with a separator at both ends. -/
def framed (w : List α) : List (Option α) := interleave w ++ [none]

/-- The spelling with an original letter at both ends, for a nonempty word. -/
def unframed : List α → List (Option α)
  | [] => []
  | a :: w => some a :: interleave w

def erase (w : List (Option α)) : List α := w.filterMap id

def PalindromicFactor (w v : List α) : Prop :=
  v ≠ [] ∧ v <:+: w ∧ v.reverse = v

theorem interleave_append (x y : List α) :
    interleave (x ++ y) = interleave x ++ interleave y := by
  induction x with
  | nil => rfl
  | cons a x ih => simp [interleave, ih]

@[simp] theorem erase_interleave (w : List α) : erase (interleave w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [erase, interleave] at ih ⊢
    exact ih

@[simp] theorem erase_framed (w : List α) : erase (framed w) = w := by
  simpa [framed, erase] using erase_interleave w

@[simp] theorem erase_unframed (w : List α) : erase (unframed w) = w := by
  cases w with
  | nil => rfl
  | cons a w => simpa [unframed, erase] using erase_interleave w

private theorem erase_reverse (w : List (Option α)) : erase w.reverse = (erase w).reverse := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [erase] at ih
    cases a <;> simp [erase, ih]

private theorem framed_reverse (w : List α) : (framed w).reverse = framed w.reverse := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (none :: some a :: framed w).reverse = _
    rw [List.reverse_cons, List.reverse_cons, ih, List.reverse_cons]
    simp [interleave_append, interleave, framed, List.append_assoc]

private theorem frame_unframed {w : List α} (hw : w ≠ []) :
    none :: unframed w ++ [none] = framed w := by
  cases w with
  | nil => contradiction
  | cons a w => rfl

private theorem unframed_reverse_of_palindrome {w : List α} (hw : w ≠ [])
    (hp : w.reverse = w) : (unframed w).reverse = unframed w := by
  have hf := framed_reverse w
  rw [hp, ← frame_unframed hw] at hf
  simpa [List.reverse_append, List.append_assoc] using hf

/-- The Boolean state records whether the next symbol is an original letter. -/
private inductive Alternates : Bool → List (Option α) → Bool → Prop
  | nil (s) : Alternates s [] s
  | separator : Alternates true w t → Alternates false (none :: w) t
  | letter (a : α) : Alternates false w t → Alternates true (some a :: w) t

private theorem alternating_append {u v : List (Option α)} {r s t : Bool}
    (hu : Alternates r u s) (hv : Alternates s v t) :
    Alternates r (u ++ v) t := by
  induction hu with
  | nil => exact hv
  | separator _ ih => exact .separator (ih hv)
  | letter a _ ih => exact .letter a (ih hv)

private theorem alternating_split {u v : List (Option α)} {r t : Bool}
    (h : Alternates r (u ++ v) t) :
    ∃ s, Alternates r u s ∧ Alternates s v t := by
  induction u generalizing r with
  | nil => exact ⟨r, .nil r, h⟩
  | cons a u ih =>
    cases h with
    | separator h =>
      obtain ⟨s, h₁, h₂⟩ := ih h
      exact ⟨s, .separator h₁, h₂⟩
    | letter a h =>
      obtain ⟨s, h₁, h₂⟩ := ih h
      exact ⟨s, .letter a h₁, h₂⟩

private theorem alternating_framed (w : List α) : Alternates false (framed w) true := by
  induction w with
  | nil => exact .separator (.nil true)
  | cons a w ih => exact .separator (.letter a ih)

private theorem alternating_reverse {w : List (Option α)} {s t : Bool}
    (h : Alternates s w t) : Alternates (!t) w.reverse (!s) := by
  induction h with
  | nil s => exact .nil (!s)
  | separator _ ih =>
    rw [List.reverse_cons]
    exact alternating_append ih (.separator (.nil true))
  | letter a _ ih =>
    rw [List.reverse_cons]
    exact alternating_append ih (.letter a (.nil false))

private theorem alternating_unique_start {w : List (Option α)} (hw : w ≠ [])
    {s t s' t' : Bool} (h : Alternates s w t) (h' : Alternates s' w t') : s = s' := by
  cases h with
  | nil => contradiction
  | separator => cases h'; rfl
  | letter => cases h'; rfl

private theorem spell_from_separator {w : List (Option α)} {t : Bool}
    (h : Alternates false w t) :
    w = interleave (erase w) ++ (if t then [none] else []) := by
  match w with
  | [] => cases h; rfl
  | [a] => cases h with
    | separator h => cases h; rfl
  | a :: b :: w =>
    cases h with
    | separator h =>
      cases h with
      | letter b h =>
        have hr := spell_from_separator h
        change none :: some b :: w = none :: some b ::
          (interleave (erase w) ++ (if t then [none] else []))
        rw [← hr]
termination_by w.length

private theorem spell_from_letter {w : List (Option α)}
    (h : Alternates true w false) : w = unframed (erase w) := by
  cases h with
  | letter a h =>
    have hw := spell_from_separator h
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at hw
    change some a :: _ = some a :: interleave (erase _)
    rw [← hw]

private theorem palindromic_alternating_spelling {w : List (Option α)} {s t : Bool}
    (h : Alternates s w t) (hw : w ≠ []) (hp : w.reverse = w) :
    w = framed (erase w) ∨ w = unframed (erase w) := by
  have hr := alternating_reverse h
  rw [hp] at hr
  have hb := alternating_unique_start hw h hr
  cases s <;> cases t <;> simp at hb
  · exact .inl (spell_from_separator h)
  · exact .inr (spell_from_letter h)

private theorem framed_infix {u w : List α} (h : u <:+: w) :
    framed u <:+: framed w := by
  obtain ⟨l, r, rfl⟩ := h
  have ⟨tail, ht⟩ : ∃ tail, framed r = none :: tail := by
    cases r
    · exact ⟨[], rfl⟩
    · exact ⟨_, rfl⟩
  refine ⟨interleave l, tail, ?_⟩
  simp only [framed, interleave_append, List.append_assoc]
  change interleave l ++ (interleave u ++ (none :: tail)) =
    interleave l ++ (interleave u ++ framed r)
  rw [ht]

private theorem framed_nonempty (u : List α) : framed u ≠ [] := by
  simp [framed]

private theorem unframed_nonempty {u : List α} (hu : u ≠ []) : unframed u ≠ [] := by
  cases u <;> simp_all [unframed]

private theorem singleton_separator (w : List α) : PalindromicFactor (framed w) [none] := by
  refine ⟨by simp, ?_, rfl⟩
  have hf : framed ([] : List α) <:+: framed w := framed_infix
    (show ([] : List α) <:+: w from ⟨[], w, rfl⟩)
  exact hf

private theorem pal_framed_infix {w u : List α} (h : PalindromicFactor w u) :
    PalindromicFactor (framed w) (framed u) := by
  refine ⟨framed_nonempty u, framed_infix h.2.1, ?_⟩
  rw [framed_reverse, h.2.2]

private theorem pal_unframed_infix {w u : List α} (h : PalindromicFactor w u) :
    PalindromicFactor (framed w) (unframed u) := by
  refine ⟨unframed_nonempty h.1, ?_, unframed_reverse_of_palindrome h.1 h.2.2⟩
  have hsub : unframed u <:+: framed u := ⟨[none], [none], frame_unframed h.1⟩
  exact hsub.trans (framed_infix h.2.1)

/-- The language-level statement of `lem:insertcount`: a nonempty
palindromic factor of the framed word is the separator or one of the
two spellings of a nonempty palindromic factor of the original word. -/
theorem palindromicFactor_framed_iff (w : List α) (u : List (Option α)) :
    PalindromicFactor (framed w) u ↔
      u = [none] ∨ ∃ v, PalindromicFactor w v ∧ (u = framed v ∨ u = unframed v) := by
  constructor
  · rintro ⟨hu, hinfix, hp⟩
    obtain ⟨l, r, hr⟩ := hinfix
    have hpath := alternating_framed w
    rw [← hr, List.append_assoc] at hpath
    obtain ⟨_, _, htail⟩ := alternating_split hpath
    obtain ⟨_, hmid, _⟩ := alternating_split htail
    have hspell := palindromic_alternating_spelling hmid hu hp
    by_cases he : erase u = []
    · rcases hspell with hf | hb
      · exact .inl (by rw [hf, he]; rfl)
      · exfalso
        exact hu (by rw [hb, he]; rfl)
    · have hf := List.IsInfix.filterMap id (show u <:+: framed w from ⟨l, r, hr⟩)
      change erase u <:+: erase (framed w) at hf
      rw [erase_framed] at hf
      have hrev := congrArg erase hp
      rw [erase_reverse] at hrev
      exact .inr ⟨erase u, ⟨he, hf, hrev⟩, hspell⟩
  · rintro (rfl | ⟨v, hv, rfl | rfl⟩)
    · exact singleton_separator w
    · exact pal_framed_infix hv
    · exact pal_unframed_infix hv

/-- A duplicate-free enumeration of the nonempty palindromic factors. -/
def Enumerates (w : List α) (factors : List (List α)) : Prop :=
  factors.Nodup ∧ ∀ v, v ∈ factors ↔ PalindromicFactor w v

private theorem framed_head (w : List α) : (framed w).head? = some none := by
  cases w <;> rfl

private theorem unframed_head {w : List α} (hw : w ≠ []) :
    ∃ a, (unframed w).head? = some (some a) := by
  cases w with
  | nil => contradiction
  | cons a w => exact ⟨a, rfl⟩

private theorem nodup_map_of_injective {xs : List α} (h : xs.Nodup) (f : α → β)
    (hinj : ∀ {x y}, f x = f y → x = y) : (xs.map f).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact h.imp (fun hne he => hne (hinj he))

/-- A duplicate-free list of the factors of the framed word, obtained
from any duplicate-free list of factors of the original word. -/
def framedEnumeration (ps : List (List α)) : List (List (Option α)) :=
  [none] :: (ps.map framed ++ ps.map unframed)

theorem enumerates_framed {w : List α} {ps : List (List α)} (h : Enumerates w ps) :
    Enumerates (framed w) (framedEnumeration ps) := by
  have hnonempty : ∀ v ∈ ps, v ≠ [] := fun v hv => ((h.2 v).1 hv).1
  constructor
  · unfold framedEnumeration
    rw [List.nodup_cons]
    constructor
    · intro hmem
      simp only [List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨v, hv, hv'⟩ | ⟨v, hv, hv'⟩ <;>
        have he := congrArg erase hv' <;>
        simp only [erase_framed, erase_unframed] at he <;>
        exact hnonempty v hv he
    · rw [List.Nodup, List.pairwise_append]
      refine ⟨nodup_map_of_injective h.1 framed ?_, nodup_map_of_injective h.1 unframed ?_, ?_⟩
      · intro x y he
        simpa using congrArg erase he
      · intro x y he
        simpa using congrArg erase he
      · intro x hx y hy
        obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
        obtain ⟨a, ha⟩ := unframed_head (hnonempty u hu)
        intro he
        have hh := congrArg List.head? he
        rw [framed_head, ha] at hh
        cases Option.some.inj hh
  · intro v
    rw [palindromicFactor_framed_iff]
    simp only [framedEnumeration, List.mem_cons, List.mem_append, List.mem_map, h.2]
    constructor
    · rintro (rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact .inl rfl
      · exact .inr ⟨u, hu, .inl rfl⟩
      · exact .inr ⟨u, hu, .inr rfl⟩
    · rintro (rfl | ⟨u, hu, rfl | rfl⟩)
      · exact .inl rfl
      · exact .inr (.inl ⟨u, hu, rfl⟩)
      · exact .inr (.inr ⟨u, hu, rfl⟩)

theorem length_framedEnumeration (ps : List (List α)) :
    (framedEnumeration ps).length = 1 + 2 * ps.length := by
  simp [framedEnumeration]
  omega

private def candidates (w : List α) : List (List α) :=
  (List.range (w.length + 1)).flatMap fun k =>
    (List.range ((w.drop k).length + 1)).map fun m => (w.drop k).take m

private theorem infix_mem_candidates {w v : List α} (h : v <:+: w) :
    v ∈ candidates w := by
  obtain ⟨left, right, rfl⟩ := h
  simp only [candidates, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨left.length, by simp; omega, v.length, ?_, ?_⟩
  · rw [List.append_assoc, List.drop_left, List.length_append]
    omega
  · rw [List.append_assoc, List.drop_left, List.take_left]

private theorem exists_nodup_enumeration (xs : List β) (p : β → Prop)
    (h : ∀ x, p x → x ∈ xs) :
    ∃ ys : List β, ys.Nodup ∧ ∀ x, x ∈ ys ↔ p x := by
  classical
  induction xs generalizing p with
  | nil =>
    refine ⟨[], List.nodup_nil, ?_⟩
    intro x
    simp only [List.not_mem_nil, false_iff]
    exact fun hx => List.not_mem_nil (h x hx)
  | cons a xs ih =>
    have hx : ∀ x, p x ∧ x ≠ a → x ∈ xs := by
      intro x hx
      exact (List.mem_cons.mp (h x hx.1)).resolve_left hx.2
    obtain ⟨ys, hnodup, hys⟩ := ih (fun x => p x ∧ x ≠ a) hx
    by_cases ha : p a
    · have hnew : a ∉ ys := fun hm => ((hys a).1 hm).2 rfl
      refine ⟨a :: ys, List.nodup_cons.mpr ⟨hnew, hnodup⟩, ?_⟩
      intro x
      by_cases he : x = a
      · subst x
        simp [ha]
      · simp [List.mem_cons, hys, he]
    · refine ⟨ys, hnodup, ?_⟩
      intro x
      by_cases he : x = a
      · subst x
        simp [hys, ha]
      · simp [hys, he]

theorem exists_enumeration (w : List α) : ∃ ps, Enumerates w ps := by
  exact exists_nodup_enumeration (candidates w) (PalindromicFactor w)
    (fun _ h => infix_mem_candidates h.2.1)

private theorem enumeration_size_unique {w : List α} {ps qs : List (List α)}
    (hp : Enumerates w ps) (hq : Enumerates w qs) : ps.length = qs.length := by
  classical
  apply Nat.le_antisymm
  · exact FiniteList.nodup_length_le_of_subset hp.1 (fun v hv => (hq.2 v).2 ((hp.2 v).1 hv))
  · exact FiniteList.nodup_length_le_of_subset hq.1 (fun v hv => (hp.2 v).2 ((hq.2 v).1 hv))

/-- The number of distinct palindromic factors after framing is twice
the original number plus one. Counts may come from any enumerations. -/
theorem framed_factor_count {w : List α} {ps : List (List α)} {qs : List (List (Option α))}
    (hp : Enumerates w ps) (hq : Enumerates (framed w) qs) :
    qs.length = 1 + 2 * ps.length := by
  rw [enumeration_size_unique hq (enumerates_framed hp), length_framedEnumeration]

/-- A rich word has as many distinct nonempty palindromic factors as letters. -/
def Rich (w : List α) : Prop :=
  ∃ ps, Enumerates w ps ∧ ps.length = w.length

theorem length_interleave (w : List α) : (interleave w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [interleave, List.length_cons, ih]
    omega

theorem length_framed (w : List α) : (framed w).length = 1 + 2 * w.length := by
  simp [framed, length_interleave]
  omega

/-- The richness equivalence in `lem:insertcount`. -/
theorem rich_framed_iff (w : List α) : Rich (framed w) ↔ Rich w := by
  constructor
  · rintro ⟨qs, hqs, hq⟩
    obtain ⟨ps, hps⟩ := exists_enumeration w
    have he := framed_factor_count hps hqs
    rw [hq, length_framed] at he
    exact ⟨ps, hps, by omega⟩
  · rintro ⟨ps, hps, hl⟩
    refine ⟨framedEnumeration ps, enumerates_framed hps, ?_⟩
    rw [length_framedEnumeration, length_framed, hl]

private theorem infix_before_last {w l v r : List α} {a : α}
    (h : l ++ v ++ r = w ++ [a]) (hr : r ≠ []) : v <:+: w := by
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have hr' : 0 < r.length := List.length_pos_iff.mpr hr
  have hpre : l ++ v <+: w := List.prefix_of_prefix_length_le ⟨r, h⟩
    (List.prefix_append w [a]) (by simp only [List.length_append]; omega)
  obtain ⟨tail, ht⟩ := hpre
  exact ⟨l, tail, ht⟩

private theorem new_palindrome_suffix {w v : List α} {a : α}
    (hv : PalindromicFactor (w ++ [a]) v) (hnew : ¬ PalindromicFactor w v) :
    v <:+ w ++ [a] := by
  obtain ⟨l, r, hr⟩ := hv.2.1
  by_cases h : r = []
  · exact ⟨l, by simpa [h] using hr⟩
  · exact False.elim (hnew ⟨hv.1, infix_before_last hr h, hv.2.2⟩)

private theorem new_palindrome_unique {w u v : List α} {a : α}
    (hu : PalindromicFactor (w ++ [a]) u) (hv : PalindromicFactor (w ++ [a]) v)
    (hunew : ¬ PalindromicFactor w u) (hvnew : ¬ PalindromicFactor w v) :
    u = v := by
  have hus := new_palindrome_suffix hu hunew
  have hvs := new_palindrome_suffix hv hvnew
  have hsame {small large : List α}
      (hs : PalindromicFactor (w ++ [a]) small)
      (hl : PalindromicFactor (w ++ [a]) large)
      (hsnew : ¬ PalindromicFactor w small)
      (hls : large <:+ w ++ [a]) (hsl : small <:+ large) : small = large := by
    have hp := hsl.reverse
    rw [hs.2.2, hl.2.2] at hp
    obtain ⟨r, hr⟩ := hp
    by_cases he : r = []
    · simpa [he] using hr
    · obtain ⟨l, hlast⟩ := hls
      have h : l ++ small ++ r = w ++ [a] := by rw [List.append_assoc, hr, hlast]
      exact False.elim (hsnew ⟨hs.1, infix_before_last h he, hs.2.2⟩)
  rcases List.suffix_or_suffix_of_suffix hus hvs with h | h
  · exact hsame hu hv hunew hvs h
  · exact (hsame hv hu hvnew hus h).symm

private theorem factors_grow_by_at_most_one {w : List α} {a : α}
    {ps qs : List (List α)} (hp : Enumerates w ps) (hq : Enumerates (w ++ [a]) qs) :
    qs.length ≤ ps.length + 1 := by
  classical
  by_cases hex : ∃ v ∈ qs, ¬ PalindromicFactor w v
  · obtain ⟨v, hv, hvnew⟩ := hex
    have hs : ∀ u ∈ qs, u ∈ v :: ps := by
      intro u hu
      by_cases he : PalindromicFactor w u
      · exact List.mem_cons_of_mem _ ((hp.2 u).2 he)
      · have heq := new_palindrome_unique ((hq.2 u).1 hu) ((hq.2 v).1 hv) he hvnew
        simp [heq]
    exact FiniteList.nodup_length_le_of_subset hq.1 hs
  · have hs : ∀ v ∈ qs, v ∈ ps := by
      intro v hv
      apply (hp.2 v).2
      by_cases he : PalindromicFactor w v
      · exact he
      · exact False.elim (hex ⟨v, hv, he⟩)
    exact Nat.le_trans (FiniteList.nodup_length_le_of_subset hq.1 hs) (Nat.le_succ _)

private theorem induct_append_singleton {motive : List α → Prop} (w : List α)
    (h₀ : motive []) (hs : ∀ w a, motive w → motive (w ++ [a])) : motive w := by
  have hr : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => exact h₀
    | cons a r ih =>
      rw [List.reverse_cons]
      exact hs _ _ ih
  simpa using hr w.reverse

/-- The upper bound on the number of distinct nonempty palindromic factors. -/
theorem palindromicFactor_count_le_length (w : List α) {ps : List (List α)}
    (hp : Enumerates w ps) : ps.length ≤ w.length := by
  induction w using induct_append_singleton generalizing ps with
  | h₀ =>
    cases ps with
    | nil => exact Nat.le_refl _
    | cons v ps =>
      have hv := (hp.2 v).1 (by simp)
      have hzero : v.length ≤ 0 := hv.2.1.length_le
      have hvnil : v = [] := List.length_eq_zero_iff.mp (by omega)
      exact False.elim (hv.1 hvnil)
  | hs w a ih =>
    obtain ⟨qs, hq⟩ := exists_enumeration w
    have hle := factors_grow_by_at_most_one hq hp
    have hold := ih hq
    simpa using Nat.le_trans hle (Nat.add_le_add_right hold 1)

private theorem rich_before_last {w : List α} {a : α} (h : Rich (w ++ [a])) : Rich w := by
  obtain ⟨ps, hps, hlength⟩ := h
  obtain ⟨qs, hqs⟩ := exists_enumeration w
  have h₁ := factors_grow_by_at_most_one hqs hps
  have h₂ := palindromicFactor_count_le_length w hqs
  rw [hlength, List.length_append] at h₁
  exact ⟨qs, hqs, by simpa using Nat.le_antisymm h₂ (by simpa using h₁)⟩

private theorem rich_prefix {w v : List α} (hw : Rich w) (hv : v <+: w) : Rich v := by
  obtain ⟨tail, rfl⟩ := hv
  induction tail using induct_append_singleton with
  | h₀ => simpa using hw
  | hs tail a ih =>
    rw [← List.append_assoc] at hw
    exact ih (rich_before_last hw)

private theorem rich_reverse {w : List α} (hw : Rich w) : Rich w.reverse := by
  obtain ⟨ps, hps, hl⟩ := hw
  refine ⟨ps.map List.reverse, ⟨nodup_map_of_injective hps.1 _ List.reverse_inj.mp, ?_⟩, ?_⟩
  · intro v
    constructor
    · intro h
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h
      have hp := (hps.2 u).1 hu
      refine ⟨?_, hp.2.1.reverse, ?_⟩
      · simpa using hp.1
      · rw [List.reverse_reverse, hp.2.2]
    · intro h
      have hv : PalindromicFactor w v.reverse := by
        refine ⟨?_, ?_, ?_⟩
        · simpa using h.1
        · simpa using h.2.1.reverse
        · rw [List.reverse_reverse, h.2.2]
      exact List.mem_map.2 ⟨v.reverse, (hps.2 _).2 hv, List.reverse_reverse _⟩
  · simpa using hl

/-- Every factor of a rich word is rich. -/
theorem rich_of_infix {w v : List α} (hw : Rich w) (hv : v <:+: w) : Rich v := by
  obtain ⟨left, right, rfl⟩ := hv
  have hpre := rich_prefix hw (List.prefix_append (left ++ v) right)
  have hrev := rich_reverse hpre
  rw [List.reverse_append] at hrev
  have hvrev := rich_prefix hrev (List.prefix_append v.reverse left.reverse)
  simpa using rich_reverse hvrev

/-- In a rich word, the nonempty palindromic factors whose first letter
differs from a fixed letter are counted by the positions with that property.
At each extension exactly one new palindrome appears and ends at the new
position. -/
theorem rich_nondistinguished_palindrome_count [DecidableEq α] (a : α) (w : List α)
    {ps : List (List α)} (hp : Enumerates w ps) (hsize : ps.length = w.length) :
    (ps.filter fun v => decide (v.head? ≠ some a)).length =
      (w.filter fun b => decide (b ≠ a)).length := by
  classical
  induction w using induct_append_singleton generalizing ps with
  | h₀ =>
    have he : ps = [] := List.length_eq_zero_iff.1 hsize
    simp [he]
  | hs w b ih =>
    obtain ⟨qs, hq, hlen⟩ := rich_before_last ⟨ps, hp, hsize⟩
    have hnew : ∃ v ∈ ps, ¬ PalindromicFactor w v := by
      apply Classical.byContradiction
      intro h
      have hold (v : List α) (hv : v ∈ ps) : PalindromicFactor w v := by
        apply Classical.byContradiction
        exact fun hn => h ⟨v, hv, hn⟩
      have hle := FiniteList.nodup_length_le_of_subset hp.1
        (fun v hv => (hq.2 v).2 (hold v hv))
      simp only [hsize, hlen, List.length_append, List.length_cons, List.length_nil] at hle
      omega
    obtain ⟨v, hv, hvnew⟩ := hnew
    have hvpal := (hp.2 v).1 hv
    have hhead : v.head? = some b := by
      obtain ⟨l, hl⟩ := new_palindrome_suffix hvpal hvnew
      have hlast := congrArg List.getLast? hl
      rw [List.getLast?_append, List.getLast?_append] at hlast
      rw [← hvpal.2.2, List.head?_reverse]
      cases he : v.getLast? with
      | none => exact False.elim (hvpal.1 (List.getLast?_eq_none_iff.1 he))
      | some c => simpa [he] using hlast
    have hnodup : (v :: qs).Nodup :=
      List.nodup_cons.2 ⟨fun hvq => hvnew ((hq.2 v).1 hvq), hq.1⟩
    have hmem (u : List α) : u ∈ ps ↔ u ∈ v :: qs := by
      constructor
      · intro hu
        by_cases h : PalindromicFactor w u
        · exact List.mem_cons_of_mem _ ((hq.2 u).2 h)
        · have he := new_palindrome_unique ((hp.2 u).1 hu) hvpal h hvnew
          simp [he]
      · intro hu
        rcases List.mem_cons.1 hu with (rfl | hu)
        · exact hv
        · obtain ⟨hne, hinfix, hpal⟩ := (hq.2 u).1 hu
          exact (hp.2 u).2 ⟨hne, hinfix.trans (List.prefix_append w [b]).isInfix, hpal⟩
    let p : List α → Bool := fun v => decide (v.head? ≠ some a)
    have heq : (ps.filter p).length = ((v :: qs).filter p).length := by
      apply Nat.le_antisymm
      · apply FiniteList.nodup_length_le_of_subset (hp.1.filter _)
        intro u hu
        obtain ⟨hm, hf⟩ := List.mem_filter.1 hu
        exact List.mem_filter.2 ⟨(hmem u).1 hm, hf⟩
      · apply FiniteList.nodup_length_le_of_subset (hnodup.filter _)
        intro u hu
        obtain ⟨hm, hf⟩ := List.mem_filter.1 hu
        exact List.mem_filter.2 ⟨(hmem u).2 hm, hf⟩
    change (ps.filter p).length = _
    rw [heq, List.filter_cons, List.filter_append, List.length_append]
    by_cases h : b = a <;> simp [p, hhead, h, Nat.add_comm] <;> simpa using ih hq hlen

end Thesis.PalindromeFactors
