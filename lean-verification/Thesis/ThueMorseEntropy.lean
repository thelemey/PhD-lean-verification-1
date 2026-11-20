import Thesis.ThueMorseComplexity
import Thesis.WordOrbitClosure
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
import Mathlib.Topology.UniformSpace.DiscreteUniformity
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.FieldSimp

open Set Filter Dynamics UniformSpace
open scoped Topology Uniformity ENNReal

namespace Thesis.ThueMorse

variable {A : Type*} [UniformSpace A] [DiscreteUniformity A] [Fintype A]

private def prefixEntourage (m : Nat) : Set ((Nat → A) × (Nat → A)) :=
  {xy | ∀ i < m, xy.1 i = xy.2 i}

omit [Fintype A] in
private theorem prefix_entourage_subset {U : Set ((Nat → A) × (Nat → A))}
    (hU : U ∈ 𝓤 (Nat → A)) : ∃ m, prefixEntourage m ⊆ U := by
  rw [Pi.uniformity] at hU
  obtain ⟨I, hI, V, hV, he⟩ := Filter.mem_iInf.1 hU
  let J := hI.toFinset
  refine ⟨J.sup id + 1, fun xy hxy => ?_⟩
  rw [he, mem_iInter]
  intro i
  have h := hV i
  rw [DiscreteUniformity.eq_principal_idRel, Filter.comap_principal,
    Filter.mem_principal] at h
  apply h
  have hi : (i : Nat) ∈ J := hI.mem_toFinset.2 i.2
  have hlt : (i : Nat) < J.sup id + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  exact hxy i hlt

omit [UniformSpace A] [DiscreteUniformity A] [Fintype A] in
private theorem prefix_symmetric (m : Nat) :
    IsSymmetricRel (prefixEntourage (A := A) m) := by
  ext xy
  constructor <;> intro h i hi <;> exact (h i hi).symm

omit [UniformSpace A] [DiscreteUniformity A] [Fintype A] in
private theorem prefix_comp (m : Nat) :
    prefixEntourage (A := A) m ○ prefixEntourage m = prefixEntourage m := by
  ext xy
  constructor
  · rintro ⟨z, hxz, hzy⟩ i hi
    exact (hxz i hi).trans (hzy i hi)
  · intro h
    exact ⟨xy.1, fun _ _ => rfl, h⟩

omit [UniformSpace A] [DiscreteUniformity A] in
private theorem has_prefix_cover (w : Nat → A) (F : Set (Nat → A))
    (hF : ∀ x ∈ F, ∀ k, ∃ i, window w k i = window x k 0) (n m : Nat) :
    ∃ s : Finset (Nat → A),
      IsDynCoverOf (fun x => shiftBy x 1) F (prefixEntourage m) n s ∧
      s.card ≤ complexity w (n + m) := by
  classical
  let L := factorLanguage w (n + m)
  let rep := fun u : Fin (n + m) → A =>
    if hu : u ∈ L then shiftBy w ((mem_factorLanguage _ _ _).1 hu).choose else w
  let s := L.image rep
  refine ⟨s, ?_, Finset.card_image_le⟩
  intro x hx
  let u := window x (n + m) 0
  obtain ⟨j, hj⟩ := hF x hx (n + m)
  have hu : u ∈ L := (mem_factorLanguage _ _ _).2 ⟨j, hj⟩
  have hr : rep u ∈ s := Finset.mem_image.2 ⟨u, hu, rfl⟩
  apply Set.mem_iUnion₂.2
  refine ⟨rep u, hr, ?_⟩
  rw [mem_ball_dynEntourage]
  intro k hk
  rw [shift_iterate, shift_iterate]
  intro i hi
  have he := congrFun ((mem_factorLanguage _ _ _).1 hu).choose_spec
    ⟨k + i, by omega⟩
  simp only [rep, dif_pos hu, shiftBy, Nat.add_assoc]
  simpa [window, u, Nat.add_assoc] using he

private theorem log_shifted_complexity_over_length_zero {b N : Nat} (hb : 1 < b)
    (hN : 0 < N) (haper : ¬ N ∣ b - 1) (m : Nat) :
    Tendsto (fun n : Nat =>
      Real.log (complexity (finiteWord b N hN) (n + m) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h₁ := (complexity_entropy_rate_zero hb hN haper).comp (tendsto_add_atTop_nat m)
  have h₂ := (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)).const_add 1
  have ht := h₁.mul h₂
  simp only [add_zero, zero_mul] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnm : (0 : ℝ) < (n : ℝ) + m := by positivity
  simp only [Function.comp_apply, Nat.cast_add]
  field_simp [hnR, hnm.ne']

/-- The language bound forces the topological entropy of the one-sided
digit-sum subshift to be zero, in mathlib's cover-entropy definition. -/
theorem finiteWord_topological_entropy_zero {b N : Nat} [UniformSpace (Fin N)]
    [DiscreteUniformity (Fin N)] (hb : 1 < b) (hN : 0 < N) (haper : ¬ N ∣ b - 1) :
    coverEntropy (fun x => shiftBy x 1) (wordOrbitClosure (finiteWord b N hN)) = 0 := by
  let w := finiteWord b N hN
  let F := wordOrbitClosure w
  let T : (Nat → Fin N) → (Nat → Fin N) := fun x => shiftBy x 1
  have hn : F.Nonempty := ⟨w, (mem_wordOrbitClosure_iff w w).2 (fun _ => ⟨0, rfl⟩)⟩
  have hshift : MapsTo T F F := fun _ hx => wordOrbitClosure_shift_mem hx
  apply le_antisymm _ (coverEntropy_nonneg T hn)
  change coverEntropy T F ≤ 0
  unfold coverEntropy
  refine iSup₂_le fun U hU => ?_
  obtain ⟨m, hm⟩ := prefix_entourage_subset hU
  refine (coverEntropyEntourage_antitone T F hm).trans ?_
  have hzero := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (log_shifted_complexity_over_length_zero hb hN haper m)
  apply ge_of_tendsto hzero
  filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
  obtain ⟨s, hs, hcard⟩ := has_prefix_cover w F
    (fun x hx => (mem_wordOrbitClosure_iff w x).1 hx) n m
  change IsDynCoverOf T F (prefixEntourage m) n (s : Set (Nat → Fin N)) at hs
  have h := IsDynCoverOf.coverEntropyEntourage_le_log_card_div (s := s) hshift
    (prefix_symmetric m) hn.ne' hs
  rw [prefix_comp] at h
  refine h.trans ?_
  have hlog : ENNReal.log (s.card : ℝ≥0∞) ≤
      ENNReal.log (complexity w (n + m) : ℝ≥0∞) := ENNReal.log_monotone (by exact_mod_cast hcard)
  have hc : 0 < (complexity w (n + m) : ℝ) := by
    have h' := (complexity_bounds hb hN (k := n + m) (by omega) haper).1
    change n + m + 1 ≤ complexity w (n + m) at h'
    exact_mod_cast (show 0 < complexity w (n + m) by omega)
  rw [show (complexity w (n + m) : ℝ≥0∞) =
    ENNReal.ofReal (complexity w (n + m) : ℝ) from (ENNReal.ofReal_natCast _).symm,
    ENNReal.log_ofReal_of_pos hc] at hlog
  exact EReal.div_le_div_right_of_nonneg (by exact_mod_cast Nat.zero_le n) hlog

end Thesis.ThueMorse
