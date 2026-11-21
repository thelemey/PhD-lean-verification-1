import Thesis.SturmianRichness
import Thesis.SturmianFactorTree

namespace Thesis.FactorTree

open PalindromeFactors ThueMorse

/-- Which of the first k cumulative floors have crossed an integer when the
intercept moves from zero to t? The sets grow by inclusion as t grows. -/
private noncomputable def crossed (a : ℝ) (k : Nat) (t : ℝ) : Finset (Fin k) :=
  Finset.univ.filter fun j => mechanicalFloor a 0 (j.val+1) < mechanicalFloor a t (j.val+1)

private theorem crossed_mono (a : ℝ) (k : Nat) {s t : ℝ} (h : s ≤ t) :
    crossed a k s ⊆ crossed a k t := by
  intro j hj
  simp only [crossed, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.trans_le (Int.floor_mono (add_le_add_right h _))

private theorem same_prefix_of_crossed_card (a : ℝ) (k : Nat) {s t : ℝ}
    (hs : s ∈ Set.Ico 0 1) (ht : t ∈ Set.Ico 0 1)
    (h : (crossed a k s).card = (crossed a k t).card) :
    (fun j : Fin k => mechanicalLetter a s j) = fun j : Fin k => mechanicalLetter a t j := by
  have hsets : crossed a k s = crossed a k t := by
    rcases le_total s t with hst | hts
    · exact Finset.eq_of_subset_of_card_le (crossed_mono a k hst) h.ge
    · exact (Finset.eq_of_subset_of_card_le (crossed_mono a k hts) h.le).symm
  have bounds (r : ℝ) (hr : r ∈ Set.Ico 0 1) (j : Nat) :
      mechanicalFloor a 0 j ≤ mechanicalFloor a r j ∧
        mechanicalFloor a r j ≤ mechanicalFloor a 0 j + 1 := by
    simp only [mechanicalFloor, zero_add]
    constructor
    · exact Int.floor_mono (le_add_of_nonneg_left hr.1)
    · rw [Int.floor_le_iff]
      push_cast
      linarith [Int.lt_floor_add_one ((j : ℝ)*a), hr.2]
  have eqat (j : Nat) (hj : j ≤ k) : mechanicalFloor a s j = mechanicalFloor a t j := by
    cases j with
    | zero => simp [mechanicalFloor, Int.floor_eq_zero_iff.2 hs, Int.floor_eq_zero_iff.2 ht]
    | succ j =>
      have he : (⟨j, by omega⟩ : Fin k) ∈ crossed a k s ↔ (⟨j, by omega⟩ : Fin k) ∈ crossed a k t := by rw [hsets]
      simp only [crossed, Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨hs₁, hs₂⟩ := bounds s hs (j+1)
      obtain ⟨ht₁, ht₂⟩ := bounds t ht (j+1)
      omega
  funext j
  simp only [mechanicalLetter, eqat _ (Nat.succ_le_of_lt j.isLt), eqat _ j.isLt.le]

/-- Every finite lower mechanical prefix occurs in the characteristic word
of the same slope. The characteristic language already has k+1 elements;
the number of crossed floors distinguishes them and has just k+1 values. -/
theorem lower_prefix_mem_characteristic {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hi : Irrational a) {t : ℝ} (ht : t ∈ Set.Ico 0 1) (k : Nat) :
    (fun j : Fin k => mechanicalLetter a t j) ∈ factorLanguage (characteristicWord a) k := by
  classical
  let L := factorLanguage (characteristicWord a) k
  have rep (u : L) : ∃ s ∈ Set.Ico (0:ℝ) 1, (fun j : Fin k => mechanicalLetter a s j) = u.val := by
    obtain ⟨i, he⟩ := (mem_factorLanguage _ _ _).1 u.property
    exact ⟨_, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, (characteristic_window_eq_fract a i k).symm.trans he⟩
  choose s hs he using rep
  let code (t : ℝ) : Fin (k+1) := ⟨(crossed a k t).card, Nat.lt_succ_of_le (by
    simpa using (Finset.card_le_univ (crossed a k t)))⟩
  have hinj : Function.Injective (fun u : L => code (s u)) := by
    intro u v huv
    exact Subtype.ext ((he u).symm.trans ((same_prefix_of_crossed_card a k (hs u) (hs v)
      (congrArg Fin.val huv)).trans (he v)))
  have hcard : Fintype.card L = Fintype.card (Fin (k+1)) := by
    simpa only [L, Fintype.card_coe, Fintype.card_fin, complexity] using characteristic_complexity a ha ha' hi k
  obtain ⟨u, hu⟩ := ((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2 (code t)
  rw [← (same_prefix_of_crossed_card a k (hs u) ht (congrArg Fin.val hu)), he u]
  exact u.property

theorem mechanicalLetter_infiniteRich {a : ℝ} (ha : 0 < a) (ha' : a < 1) (hi : Irrational a)
    (t : ℝ) : InfiniteRich (mechanicalLetter a t) := by
  intro i n
  let r := t + (i : ℝ)*a
  have letters (j : Nat) : mechanicalLetter a t (i+j) = mechanicalLetter a (Int.fract r) j := by
    have hs : mechanicalLetter a t (i+j) = mechanicalLetter a r j := by
      simp only [mechanicalLetter, mechanicalFloor, r, Nat.cast_add, Nat.cast_one]
      congr 1
      congr 1 <;> ring_nf
    rw [hs]
    have he := mechanicalLetter_int_shift a (Int.fract r) ⌊r⌋ j
    rw [Int.fract_add_floor] at he
    exact he
  obtain ⟨m, hm⟩ := (mem_factorLanguage _ _ _).1 (lower_prefix_mem_characteristic ha ha' hi
    ⟨Int.fract_nonneg r, Int.fract_lt_one r⟩ n)
  have he : factorList (mechanicalLetter a t) i n = factorList (characteristicWord a) m n := by
    unfold factorList
    congr 1
    funext j
    exact (letters j).trans (congrFun hm j).symm
  rw [he]
  exact characteristicWord_infiniteRich ha ha' hi m n

/-- The upper mechanical coding in deffSturmiann1. -/
noncomputable def upperMechanicalLetter (a t : ℝ) (j : Nat) : Bool :=
  decide (⌈t + ((j:ℝ)+1)*a⌉ = ⌈t+(j:ℝ)*a⌉ + 1)

private theorem upper_eq_complement_lower {a : ℝ} (ha : 0 < a) (ha' : a < 1) (t : ℝ)
    (j : Nat) : upperMechanicalLetter a t j = !(mechanicalLetter (1-a) (-t) j) := by
  have hf (k : Nat) : mechanicalFloor (1-a) (-t) k = (k : ℤ)-⌈t+(k:ℝ)*a⌉ := by
    rw [mechanicalFloor, show -t+(k:ℝ)*(1-a) = -(t+(k:ℝ)*a)+k by ring, Int.floor_add_natCast,
      Int.floor_neg]
    omega
  have h := mechanicalFloor_step_eq (1-a) (-t) j (by linarith) (by linarith)
  rw [hf, hf] at h
  unfold upperMechanicalLetter
  push_cast at h
  cases he : mechanicalLetter (1-a) (-t) j <;> simp [he] at h ⊢ <;> omega

/-- Both mechanical codings and all intercepts from the dissertation's
definition have rich finite factors. -/
theorem upperMechanicalLetter_infiniteRich {a : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hi : Irrational a) (t : ℝ) : InfiniteRich (upperMechanicalLetter a t) := by
  have h := mechanicalLetter_infiniteRich (a := 1-a) (by linarith) (by linarith)
    (by simpa using hi.natCast_sub 1) (-t)
  let e : Bool ≃ Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩
  intro i n
  have he : (factorList (mechanicalLetter (1-a) (-t)) i n).map e = factorList (upperMechanicalLetter a t) i n := by
    apply List.ext_getElem (by simp [factorList])
    intro j _ _
    simp only [List.getElem_map, factorList, List.getElem_ofFn, upper_eq_complement_lower ha ha' t]
    rfl
  exact he ▸ rich_rename e (h i n)

end Thesis.FactorTree
