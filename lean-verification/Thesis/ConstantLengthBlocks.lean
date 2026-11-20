import Thesis.ThueMorseSubstitution
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace Thesis.ThueMorse

variable {A : Type*} {b : Nat}

/-- A fixed word is tiled by the aligned blocks of each substitution iterate. -/
theorem fixedWord_iterate_block (hb : 0 < b) (σ : A → Fin b → A) (w : Nat → A)
    (hw : SubstitutionFixedWord σ w) (k m : Nat) (r : Fin (b ^ k)) :
    w (b ^ k * m + r.val) = iterateSubstitution hb σ k (w m) r := by
  induction k with
  | zero =>
    have he : r.val = 0 := by have := r.isLt; simp only [pow_zero] at this; omega
    simp [he, iterateSubstitution]
  | succ k ih =>
    have hq : r.val / b < b ^ k := (Nat.div_lt_iff_lt_mul hb).2
      (by simpa only [pow_succ] using r.isLt)
    have hr : r.val % b < b := Nat.mod_lt _ hb
    have he (j : Nat) : b ^ (k + 1) * m + j = b * (b ^ k * m + j / b) + j % b := by
      rw [pow_succ, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm b (b ^ k), Nat.add_assoc]
      congr 1
      exact (by rw [Nat.add_comm, Nat.mod_add_div])
    rw [he r.val, hw _ ⟨_, hr⟩, ih ⟨_, hq⟩]
    rfl

/-- Interpret a block index and an offset as an index in a concatenation. -/
def substitutionBlockIndex (b r t : Nat) : Fin (b ^ r) × Fin (b ^ t) ≃ Fin (b ^ (r + t)) :=
  finProdFinEquiv.trans (finCongr ((pow_add b r t).symm))

theorem substitutionBlockIndex_val (b r t : Nat) (i : Fin (b ^ r)) (j : Fin (b ^ t)) :
    (substitutionBlockIndex b r t (i, j)).val = b ^ t * i.val + j.val := by
  change j.val + b ^ t * i.val = _
  exact Nat.add_comm _ _

/-- Iterating r+t times replaces each letter of the rth iterate by
its tth iterate, with the offset measured inside that block. -/
theorem iterateSubstitution_add_block (hb : 0 < b) (σ : A → Fin b → A)
    (r t : Nat) (a : A) (i : Fin (b ^ r)) (j : Fin (b ^ t)) :
    iterateSubstitution hb σ (r + t) a (substitutionBlockIndex b r t (i, j)) =
      iterateSubstitution hb σ t (iterateSubstitution hb σ r a i) j := by
  induction t with
  | zero =>
    have hj : j.val = 0 := by have := j.isLt; simp only [pow_zero] at this; omega
    change iterateSubstitution hb σ r a _ = iterateSubstitution hb σ r a i
    congr 1
    apply Fin.ext
    exact (substitutionBlockIndex_val b r 0 i j).trans (by simp [hj])
  | succ t ih =>
    let e := substitutionBlockIndex b r (t + 1) (i, j)
    have hq : j.val / b < b ^ t := (Nat.div_lt_iff_lt_mul hb).2
      (by simpa only [pow_succ] using j.isLt)
    have hdAux (p s : Nat) : (b ^ (t + 1) * p + s) / b = b ^ t * p + s / b := by
      rw [pow_succ, Nat.mul_comm (b ^ t) b, Nat.mul_assoc, Nat.mul_add_div hb]
    have hmAux (p s : Nat) : (b ^ (t + 1) * p + s) % b = s % b := by
      rw [pow_succ, Nat.mul_comm (b ^ t) b, Nat.mul_assoc]
      simp
    have hd : e.val / b = b ^ t * i.val + j.val / b := by
      simpa only [e, substitutionBlockIndex_val] using hdAux i.val j.val
    have hmod : e.val % b = j.val % b := by
      simpa only [e, substitutionBlockIndex_val] using hmAux i.val j.val
    change σ (iterateSubstitution hb σ (r + t) a ⟨e.val / b, _⟩) ⟨e.val % b, _⟩ =
      σ (iterateSubstitution hb σ t (iterateSubstitution hb σ r a i) ⟨j.val / b, _⟩) ⟨j.val % b, _⟩
    have hIndex : (⟨e.val / b, by
        apply (Nat.div_lt_iff_lt_mul hb).2
        simpa only [pow_succ] using e.isLt⟩ : Fin (b ^ (r + t))) =
        substitutionBlockIndex b r t (i, ⟨j.val / b, hq⟩) := by
      exact Fin.ext (hd.trans (substitutionBlockIndex_val b r t i ⟨j.val / b, hq⟩).symm)
    rw [hIndex, ih ⟨j.val / b, hq⟩]
    exact congrArg (σ _) (Fin.ext hmod)

end Thesis.ThueMorse
