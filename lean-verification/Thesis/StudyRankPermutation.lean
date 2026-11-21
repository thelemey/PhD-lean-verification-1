import Thesis.StudyIntegerMoments
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Dist

open Finset

namespace Thesis.StudyANCOVA

/-- Twice the pairwise rank score with midranks for ties. -/
def rankPair {α : Type*} [LinearOrder α] (a b : α) : ℕ :=
  if a < b then 2 else if a = b then 1 else 0

theorem rankPair_sum {α : Type*} [LinearOrder α] (a b : α) :
    rankPair a b + rankPair b a = 2 := by
  rcases lt_trichotomy a b with h|h|h
  · simp [rankPair,h,h.ne,not_lt_of_ge h.le,h.le,h.ne']
  · simp [rankPair,h]
  · simp [rankPair,h,h.ne,not_lt_of_ge h.le,h.le,h.ne']

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} [LinearOrder α]

/-- Twice the pooled midrank, with ranks starting at one. -/
def doubledMidrank (score : ι → α) (j : ι) : ℕ := 1 + ∑ i, rankPair (score i) (score j)

def selectedU (score : ι → α) (s : Finset ι) : ℕ :=
  ∑ j ∈ s, ∑ i ∈ univ \ s, rankPair (score i) (score j)

theorem sum_doubledMidrank_eq (score : ι → α) (s : Finset ι) :
    ∑ j ∈ s, doubledMidrank score j = selectedU score s + s.card*(s.card+1) := by
  have paired : (∑ j ∈ s, ∑ i ∈ s, rankPair (score i) (score j)) +
      (∑ i ∈ s, ∑ j ∈ s, rankPair (score j) (score i)) = 2*s.card^2 := by
    conv_lhs => rhs; rw [sum_comm]
    simp only [← sum_add_distrib,rankPair_sum,sum_const,nsmul_eq_mul,Nat.cast_id]
    ring
  have self : ∑ j ∈ s, ∑ i ∈ s, rankPair (score i) (score j) = s.card^2 := by omega
  have split (j : ι) : ∑ i, rankPair (score i) (score j) =
      (∑ i ∈ univ \ s, rankPair (score i) (score j)) + ∑ i ∈ s, rankPair (score i) (score j) :=
    (sum_sdiff (subset_univ s)).symm
  simp only [doubledMidrank,split,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,self,selectedU,Nat.cast_id]
  ring

/-- The conditional, two-sided permutation reference for two classes of the
same size. All choices of the designated class of size n are equiprobable.
For the doubled U statistic, n² is the null center. -/
def rankPermutationP (score : ι → α) (n statistic : ℕ) : ℚ :=
  let selections := (univ : Finset ι).powersetCard n
  let tail := selections.filter fun s => Nat.dist statistic (n*n) ≤ Nat.dist (selectedU score s) (n*n)
  (tail.card : ℚ)/selections.card

end Thesis.StudyANCOVA

