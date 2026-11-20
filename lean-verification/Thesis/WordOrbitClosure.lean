import Thesis.ThueMorseRecurrence
import Mathlib.Topology.Constructions

open Set

namespace Thesis.ThueMorse

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]

/-- The n-fold iterate of the one-sided shift. -/
def shiftBy (w : Nat → A) (n : Nat) : Nat → A := fun i => w (n + i)

/-- The one-sided shift orbit closure in the product topology. -/
def wordOrbitClosure (w : Nat → A) : Set (Nat → A) :=
  closure (Set.range (shiftBy w))

theorem mem_wordOrbitClosure_iff (w x : Nat → A) :
    x ∈ wordOrbitClosure w ↔ ∀ k, ∃ j, window w k j = window x k 0 := by
  constructor
  · intro hx k
    let I := Finset.range k
    let U := (I : Set Nat).pi (fun i => {x i})
    have hU : IsOpen U := isOpen_set_pi I.finite_toSet (fun _ _ => isOpen_discrete _)
    have hxU : x ∈ U := fun _ _ => rfl
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.1 hx U hU hxU
    obtain ⟨j, rfl⟩ := hz
    refine ⟨j, ?_⟩
    funext l
    have he : shiftBy w j l ∈ ({x l} : Set A) :=
      hzU l (Finset.mem_range.2 l.isLt)
    simpa [window, shiftBy] using he
  · intro h
    apply mem_closure_iff.2
    intro U hU hx
    obtain ⟨I, V, hxV, hVU⟩ := isOpen_pi_iff.1 hU x hx
    let k := I.sup id + 1
    obtain ⟨j, hj⟩ := h k
    refine ⟨shiftBy w j, hVU ?_, ⟨j, rfl⟩⟩
    intro i hi
    have hlt : i < k := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
    have he := congrFun hj ⟨i, hlt⟩
    have hx' : shiftBy w j i = x i := by simpa [window, shiftBy] using he
    rw [hx']
    exact (hxV i hi).2

theorem window_of_orbitClosure {w x : Nat → A} (hx : x ∈ wordOrbitClosure w)
    (k i : Nat) : ∃ j, window w k j = window x k i := by
  obtain ⟨j, hj⟩ := (mem_wordOrbitClosure_iff w x).1 hx (i + k)
  refine ⟨j + i, ?_⟩
  funext l
  have hl : i + l < i + k := Nat.add_lt_add_left l.isLt i
  simpa [window, Nat.add_assoc] using congrFun hj ⟨i + l, hl⟩

theorem source_window_of_uniformlyRecurrent {w x : Nat → A}
    (hx : x ∈ wordOrbitClosure w) (hr : UniformlyRecurrent w) (k i : Nat) :
    ∃ j, window x k j = window w k i := by
  obtain ⟨L, hL⟩ := hr k i
  obtain ⟨p, hp⟩ := (mem_wordOrbitClosure_iff w x).1 hx L
  obtain ⟨j, hj, hk, he⟩ := hL p
  refine ⟨j - p, ?_⟩
  funext l
  have hle : j - p + l < L := by have hl := l.isLt; omega
  have hz : p + (j - p + l) = j + l := by omega
  have hq := congrFun hp ⟨j - p + l, hle⟩
  simp only [window, Fin.val_mk, Nat.zero_add, hz] at hq
  exact hq.symm.trans (congrFun he l)

/-- Minimality in the orbit-density formulation. Each point of the
orbit closure of a uniformly recurrent word generates the same closed
shift orbit. -/
theorem wordOrbitClosure_eq_of_uniformlyRecurrent (w x : Nat → A)
    (hr : UniformlyRecurrent w) (hx : x ∈ wordOrbitClosure w) :
    wordOrbitClosure x = wordOrbitClosure w := by
  ext y
  simp only [mem_wordOrbitClosure_iff]
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    obtain ⟨j, hj⟩ := window_of_orbitClosure hx k i
    exact ⟨j, hj.trans hi⟩
  · intro h k
    obtain ⟨i, hi⟩ := h k
    obtain ⟨j, hj⟩ := source_window_of_uniformlyRecurrent hx hr k i
    exact ⟨j, hj.trans hi⟩

/-- The one-sided shift preserves the orbit closure. -/
theorem wordOrbitClosure_shift_mem {w x : Nat → A} (hx : x ∈ wordOrbitClosure w) :
    shiftBy x 1 ∈ wordOrbitClosure w := by
  apply (mem_wordOrbitClosure_iff _ _).2
  intro k
  have he : window (shiftBy x 1) k 0 = window x k 1 := by
    funext i
    simp [window, shiftBy]
  rw [he]
  exact window_of_orbitClosure hx k 1

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem shift_iterate (w : Nat → A) (n : Nat) :
    (fun x : Nat → A => shiftBy x 1)^[n] w = shiftBy w n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero, id_eq]
    funext i
    simp [shiftBy]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext j
    simp [shiftBy, Nat.add_assoc]

/-- Uniform recurrence makes the finite-alphabet digit-sum orbit closure
minimal for the one-sided shift. -/
theorem finiteWord_orbitClosure_minimal {b N : Nat} [TopologicalSpace (Fin N)]
    [DiscreteTopology (Fin N)] (hb : 1 < b) (hN : 0 < N) (x : Nat → Fin N)
    (hx : x ∈ wordOrbitClosure (finiteWord b N hN)) :
    wordOrbitClosure x = wordOrbitClosure (finiteWord b N hN) :=
  wordOrbitClosure_eq_of_uniformlyRecurrent _ x (uniformlyRecurrent_finiteWord hb hN) hx

end Thesis.ThueMorse
