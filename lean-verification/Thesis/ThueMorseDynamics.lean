import Thesis.PrimitiveSubstitutionErgodicity
import Thesis.ThueMorseEntropy
import Thesis.ThueMorseSubshift

open Dynamics

namespace Thesis.ThueMorse

/-- The five assertions of thm:dynWb for the nonperiodic case, in their
original order and for the one-sided orbit closure defined in the thesis. -/
theorem finiteWord_dynamics {b N : Nat} [UniformSpace (Fin N)] [DiscreteUniformity (Fin N)]
    [MeasurableSpace (Fin N)] [BorelSpace (Fin N)]
    (hb : 1 < b) (hN : 1 < N) (haper : ¬ N ∣ b - 1) :
    let hN₀ := Nat.zero_lt_one.trans hN
    let w := finiteWord b N hN₀
    (∀ k ≥ N - 1, ∀ a c : Fin N, ∃ j : Fin (b ^ k),
      iterateSubstitution (Nat.zero_lt_one.trans hb) (digitSubstitution b N hN₀) k a j = c) ∧
    (UniformlyRecurrent w ∧ ∀ x ∈ wordOrbitClosure w, wordOrbitClosure x = wordOrbitClosure w) ∧
    ((¬ ∃ i m : Nat, 0 < m ∧ ∀ t, w (i + t + m) = w (i + t)) ∧
      (∀ k > 0, k + 1 ≤ complexity w k ∧ complexity w k < N ^ 2 * b * k) ∧
      coverEntropy (fun x => shiftBy x 1) (wordOrbitClosure w) = 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M : Nat, ∀ n ≥ M, ∀ i c : Nat, c < N →
      |(letterCount (word b N) i n c : ℝ) - (n : ℝ) / N| < ε * (n : ℝ)) ∧
    (StrictlyErgodic w ∧ UniformFactorFrequencies w) := by
  dsimp only
  let hN₀ := Nat.zero_lt_one.trans hN
  refine ⟨iterate_digitSubstitution_contains_letter hb hN₀,
    ⟨uniformlyRecurrent_finiteWord hb hN₀, finiteWord_orbitClosure_minimal hb hN₀⟩,
    ⟨?_, fun _ hk => complexity_bounds hb hN₀ hk haper,
      finiteWord_topological_entropy_zero hb hN₀ haper⟩,
    uniform_letter_discrepancy_o hb hN, finiteWord_strictlyErgodic hb hN₀⟩
  rintro ⟨i, m, hm, hp⟩
  exact not_eventually_periodic_word hb hN₀ haper ⟨i, m, hm, fun t => congrArg Fin.val (hp t)⟩

end Thesis.ThueMorse
