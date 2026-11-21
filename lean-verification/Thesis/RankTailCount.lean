import Thesis.StudyRankPermutation
import Thesis.RankSubsetCounts

open Finset

namespace Thesis.StudyANCOVA

/-- Binary evaluation of the subset generating product. Each weight
contributes one factor, with the shift implementing multiplication by
(2^85)^weight. -/
def packedWeights : List ℕ → ℕ
  | [] => 1
  | w :: ws => let z := packedWeights ws; z + (z <<< (85*w))

theorem packedWeights_eq (ws : List ℕ) :
    packedWeights ws = (ws.map fun w => 1+(2^85:ℕ)^w).prod := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [packedWeights,List.map_cons,List.prod_cons,ih,Nat.shiftLeft_eq,pow_mul,add_mul,one_mul]
    ring

/-- The integer exponent contains the sample size and the doubled rank sum.
All pooled midranks sum to 84·85, which is below the stride 8192. -/
def rankWeight (score : Fin 84 → ℤ) (i : Fin 84) := 8192+doubledMidrank score i

def rankPrefix (packed k : ℕ) := (packed % (1 <<< (85*(k+1)))) % (2^85-1)

private theorem cardFilter {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ i ∈ s, if p i then 1 else 0 := by simp

theorem rankPermutation_count (score : Fin 84 → ℤ) (d lo hi a b packed : ℕ)
    (pos : 0 < d) (small : d ≤ 1764)
    (hl : lo+d=42*8192+3570) (hh : hi+1=42*8192+3570+d)
    (hp : packed = packedWeights ((List.finRange 84).map (rankWeight score)))
    (ha : rankPrefix packed lo = a) (hb : rankPrefix packed hi = b) :
    let n := Nat.choose 84 42
    rankPermutationP score 42 (1764+d) = ((n+a-b:ℕ):ℚ)/n := by
  let pool : Finset (Fin 84) := univ
  let all := pool.powerset
  let w := rankWeight score
  let W := fun s : Finset (Fin 84) => ∑ i ∈ s, w i
  let sel := pool.powersetCard 42
  let tail := sel.filter fun s => Nat.dist (1764+d) (42*42) ≤ Nat.dist (selectedU score s) (42*42)
  have B : pool.powerset.card < (2^85:ℕ)-1 := by simp [pool]
  have eq : pool = (List.finRange 84).toFinset := by decide +kernel
  have prod : packed = ∏ i ∈ pool, (1+(2^85:ℕ)^(w i)) := by
    rw [hp,packedWeights_eq,eq,List.prod_toFinset _ (by decide +kernel : (List.finRange 84).Nodup),List.map_map]
    rfl
  have pref (k : ℕ) : rankPrefix packed k = (all.filter fun s => W s ≤ k).card := by
    rw [rankPrefix,prod,Nat.shiftLeft_eq,one_mul,pow_mul]
    exact encoded_prefix_card pool w _ k B
  rw [pref] at ha hb
  have ranks : (∑ i, doubledMidrank score i) = 7140 := by
    simpa [selectedU] using sum_doubledMidrank_eq score univ
  have code (s : Finset (Fin 84)) : W s = s.card*8192 + ∑ i ∈ s, doubledMidrank score i := by
    simp [W,w,rankWeight,sum_add_distrib]
  have size : sel.card = Nat.choose 84 42 := by simp [sel,pool,card_powersetCard]
  have counts : tail.card + (all.filter fun s => W s ≤ hi).card =
      sel.card + (all.filter fun s => W s ≤ lo).card := by
    simp only [tail,sel,powersetCard_eq_filter,filter_filter,all,pool,cardFilter,← sum_add_distrib]
    apply sum_congr rfl
    intro s _
    have bound : ∑ i ∈ s, doubledMidrank score i ≤ 7140 := by
      rw [← ranks]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun _ _ _ => Nat.zero_le _)
    have sum := code s
    by_cases size : s.card = 42
    · have rank := sum_doubledMidrank_eq score s
      rw [size] at sum rank
      simp only [Nat.dist,size,true_and,if_true]
      split_ifs <;> omega
    · simp only [size,false_and,if_false,zero_add]
      split_ifs <;> omega
  rw [ha,hb,size] at counts
  change (tail.card:ℚ)/sel.card = _
  rw [size,show tail.card = Nat.choose 84 42+a-b by omega]

end Thesis.StudyANCOVA
