import Thesis.WordOrbitClosure
import Thesis.ThueMorseFrequency
import Thesis.ThueMorseComplexity

open Set
open scoped BigOperators

namespace Thesis.ThueMorse

/-- Every point in the digit-sum subshift has the same finite factors as W. -/
theorem orbitClosure_factorLanguage_eq {b N : Nat} [TopologicalSpace (Fin N)]
    [DiscreteTopology (Fin N)] (hb : 1 < b) (hN : 0 < N) {x : Nat → Fin N}
    (hx : x ∈ wordOrbitClosure (finiteWord b N hN)) (k : Nat) :
    factorLanguage x k = factorLanguage (finiteWord b N hN) k := by
  ext u
  simp only [mem_factorLanguage]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := window_of_orbitClosure hx k i
    exact ⟨j, hj.trans hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := source_window_of_uniformlyRecurrent hx (uniformlyRecurrent_finiteWord hb hN) k i
    exact ⟨j, hj.trans hi⟩

private theorem window_val_of_orbitClosure {b N k i : Nat} (hN : 0 < N)
    [TopologicalSpace (Fin N)] [DiscreteTopology (Fin N)] {x : Nat → Fin N}
    (hx : x ∈ wordOrbitClosure (finiteWord b N hN)) :
    ∃ j, window (word b N) k j = window (fun t => (x t).val) k i := by
  obtain ⟨j, hj⟩ := window_of_orbitClosure hx k i
  exact ⟨j, funext (fun f => congrArg Fin.val (congrFun hj f))⟩

/-- Uniform letter frequencies transfer from W to its entire orbit closure. -/
theorem orbitClosure_uniform_letter_discrepancy {b N : Nat} [TopologicalSpace (Fin N)]
    [DiscreteTopology (Fin N)] (hb : 1 < b) (hN : 1 < N) :
    ∀ ε : ℝ, 0 < ε → ∃ M : Nat, ∀ n ≥ M,
      ∀ x ∈ wordOrbitClosure (finiteWord b N (Nat.zero_lt_one.trans hN)), ∀ i c : Nat, c < N →
      |(letterCount (fun t => (x t).val) i n c : ℝ) - (n : ℝ) / N| < ε * (n : ℝ) := by
  intro ε hε
  obtain ⟨M, hM⟩ := uniform_letter_discrepancy_o hb hN ε hε
  refine ⟨M, fun n hn x hx i c hc => ?_⟩
  obtain ⟨j, hj⟩ := window_val_of_orbitClosure (Nat.zero_lt_one.trans hN) (i := i) (k := n) hx
  have he : letterCount (fun t => (x t).val) i n c = letterCount (word b N) j n c := by
    unfold letterCount
    apply Finset.sum_congr rfl
    intro t ht
    have hp := congrFun hj ⟨t, Finset.mem_range.1 ht⟩
    change word b N (j + t) = (x (i + t)).val at hp
    rw [hp]
  rw [he]
  exact hM n hn j c hc

/-- A strong twisted repeat in a point of the orbit closure would already
occur as a finite factor of W. This proves the corollary after thm:dynWb. -/
theorem orbitClosure_no_long_twisted_repeat {b N k j : Nat} [TopologicalSpace (Fin N)]
    [DiscreteTopology (Fin N)] (hb : 1 < b) (hN : 0 < N) (haper : ¬ N ∣ b - 1)
    (hk : max 2 (2 * b / positiveTwist N j) < k) (x : Nat → Fin N)
    (hx : x ∈ wordOrbitClosure (finiteWord b N hN)) :
    ¬ ∃ i m : Nat, 0 < m ∧ ∀ t < (k - 1) * m,
      (x (i + t + m)).val = ((x (i + t)).val + j) % N := by
  rintro ⟨i, m, hm, hw⟩
  obtain ⟨p, hp⟩ := window_val_of_orbitClosure hN (i := i) (k := k * m) hx
  have hkm : k * m = (k - 1) * m + m := by
    rw [← Nat.succ_mul]
    exact congrArg (· * m) (by omega)
  have hr : StrongRepeat b N k j := by
    refine ⟨p, m, hm, fun t ht => ?_⟩
    have ht₁ : t < k * m := by omega
    have ht₂ : t + m < k * m := by omega
    have h₁ := congrFun hp ⟨t, ht₁⟩
    have h₂ := congrFun hp ⟨t + m, ht₂⟩
    change word b N (p + t) = (x (i + t)).val at h₁
    change word b N (p + (t + m)) = (x (i + (t + m))).val at h₂
    rw [← Nat.add_assoc, ← Nat.add_assoc] at h₂
    rw [h₁, h₂]
    exact hw t ht
  exact (not_le_of_gt hk) (critical_bound_of_repeat hb hN haper hr)

end Thesis.ThueMorse
