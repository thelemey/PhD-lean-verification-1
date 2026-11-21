import Thesis.StudyRankPermutation

open Finset

namespace Thesis.StudyANCOVA

/-- Number of observations falling in a particular bin. -/
def binCount {n k : ℕ} (group : Fin n → Fin k) (i : Fin k) : ℕ :=
  (univ.filter fun j => group j = i).card

private theorem regroup {n k : ℕ} (bin : Fin n → Fin k) (f : Fin k → ℕ) :
    ∑ j, f (bin j) = ∑ i, binCount bin i * f i := by
  rw [← sum_fiberwise' univ bin f]
  simp [binCount]

private theorem regroup_pairs {n m k : ℕ} (a : Fin n → Fin k) (b : Fin m → Fin k)
    (weight : Fin k → Fin k → ℕ) :
    ∑ j, ∑ i, weight (a i) (b j) =
    ∑ y, binCount b y * ∑ x, binCount a x * weight x y := by
  calc
    _ = ∑ j, ∑ x, binCount a x * weight x (b j) := sum_congr rfl fun j _ => regroup a _
    _ = _ := regroup b (fun y => ∑ x, binCount a x * weight x y)

/-- For ordered bins, different-bin pairs determine their rank comparison.
Within-bin pairs can contribute a loss, a tie or a win. -/
theorem grouped_rank_bounds {α : Type*} [LinearOrder α] {n m k : ℕ}
    (a : Fin n → α) (b : Fin m → α) (bin : α → Fin k) (h : Monotone bin) :
    let lo := fun x y : Fin k => if x < y then 2 else 0
    let hi := fun x y : Fin k => if x ≤ y then 2 else 0
    let count := fun weight => ∑ y, binCount (bin ∘ b) y * ∑ x, binCount (bin ∘ a) x * weight x y
    count lo ≤ ∑ j, ∑ i, rankPair (a i) (b j) ∧ (∑ j, ∑ i, rankPair (a i) (b j)) ≤ count hi := by
  intro lo hi count
  change (∑ y, binCount (bin ∘ b) y * ∑ x, binCount (bin ∘ a) x * lo x y) ≤ _ ∧
    _ ≤ ∑ y, binCount (bin ∘ b) y * ∑ x, binCount (bin ∘ a) x * hi x y
  rw [← regroup_pairs,← regroup_pairs]
  constructor
  · apply sum_le_sum; intro j _; apply sum_le_sum; intro i _
    by_cases e : bin (a i) < bin (b j)
    · have lt := lt_of_not_ge (fun ge => not_le_of_gt e (h ge))
      simp [lo,Function.comp_def,e,rankPair,lt]
    · simp [lo,Function.comp_def,e]
  · apply sum_le_sum; intro j _; apply sum_le_sum; intro i _
    by_cases e : bin (a i) ≤ bin (b j)
    · simp only [hi,Function.comp_apply,e,if_true,rankPair]
      split_ifs <;> decide
    · have lt : b j < a i := lt_of_not_ge (fun ge => e (h ge))
      simp [hi,Function.comp_def,e,rankPair,not_lt_of_ge lt.le,lt.ne']

/-- Counts read from the two histograms in the embedded image of fig11.pdf,
from the leftmost bin to the rightmost bin. -/
def figure11Control : Fin 11 → ℕ := ![1,1,1,1,1,3,7,10,11,4,2]
def figure11Puzzles : Fin 11 → ℕ := ![0,2,0,0,0,1,4,7,9,12,7]

/-- The hundred-point post-test histogram certifies the direction of the
rank difference even without resolving any ties or ordering pairs in the
same bin. Its inputs are the displayed bin counts. -/
theorem figure11_post_rank_bounds (a b : Fin 42 → ℝ) (bin : ℝ → Fin 11) (h : Monotone bin)
    (ha : binCount (bin ∘ a) = figure11Control) (hb : binCount (bin ∘ b) = figure11Puzzles) :
    2162 ≤ ∑ j, ∑ i, rankPair (a i) (b j) ∧ (∑ j, ∑ i, rankPair (a i) (b j)) ≤ 2690 := by
  have bounds := grouped_rank_bounds a b bin h
  dsimp only at bounds
  rw [ha,hb] at bounds
  have lo : (∑ y, figure11Puzzles y * ∑ x, figure11Control x * (if x < y then 2 else 0)) = 2162 := by decide +kernel
  have hi : (∑ y, figure11Puzzles y * ∑ x, figure11Control x * (if x ≤ y then 2 else 0)) = 2690 := by decide +kernel
  simpa only [lo,hi] using bounds

end Thesis.StudyANCOVA
