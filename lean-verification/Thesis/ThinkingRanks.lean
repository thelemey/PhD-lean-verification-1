import Thesis.ThinkingGainComparison
import Thesis.RankTailCount
import Mathlib.Data.Finset.Powerset

open Finset Real

namespace Thesis.StudyANCOVA

/-- Twice the Mann–Whitney statistic for B against A. Each strict win
counts twice, each tie once. Both samples contain 42 pupils. -/
def twiceU (a b : IntegerScores) : ℕ :=
  ∑ j, ∑ i, rankPair (a i) (b j)

def ceilingCount (a : IntegerScores) : ℕ := (univ.filter fun i => a i = 12).card

def OnThinkingScale (g : IntegerPair) : Prop :=
  ∀ i, 0 ≤ g.pre i ∧ g.pre i ≤ 12 ∧ 0 ≤ g.post i ∧ g.post i ≤ 12

/-- Published constraints used in the check of the thinking-test ranks:
the scale, all twelve descriptive cells, the two paired t statistics, and
the reported numbers attaining the maximum on the post-test. -/
def MatchesThinkingReport (a b : IntegerPair) : Prop :=
  MatchesTable a.paired.summary thinkingControl ∧ MatchesTable b.paired.summary thinkingPuzzles ∧
  RoundsTo (pairedT (realScores a.gain)) 9.92 ∧ RoundsTo (pairedT (realScores b.gain)) 9.97 ∧
  ceilingCount a.post = 5 ∧ ceilingCount b.post = 9 ∧ OnThinkingScale a ∧ OnThinkingScale b

private theorem roundSqrt {x d : ℝ} (hl : (d-1/200)^2 ≤ x) (hu : x ≤ (d+1/200)^2)
    (hp : 0 ≤ d+1/200) : RoundsTo (sqrt x) d :=
  abs_le.2 ⟨by linarith only [le_sqrt_of_sq_le hl],by linarith only [sqrt_le_iff.2 ⟨hp,hu⟩]⟩

private theorem table_and_t (g : IntegerPair) (row : GroupSummary) (t : ℝ)
    (s₀ q₀ s₁ q₁ sg qg : ℤ)
    (moments : total g.pre = s₀ ∧ squareTotal g.pre = q₀ ∧ total g.post = s₁ ∧
      squareTotal g.post = q₁ ∧ total g.gain = sg ∧ squareTotal g.gain = qg)
    (check : RoundsTo ((s₀:ℝ)/42) row.pre ∧ RoundsTo ((s₁:ℝ)/42) row.post ∧
      RoundsTo ((sg:ℝ)/42) row.gain ∧ RoundsTo (sqrt (momentSS s₀ q₀/41)) row.preSD ∧
      RoundsTo (sqrt (momentSS s₁ q₁/41)) row.postSD ∧ RoundsTo (sqrt (momentSS sg qg/41)) row.gainSD ∧
      RoundsTo (sqrt (((sg:ℝ)/42)^2*42/(momentSS sg qg/41))) t)
    (pos : 0 ≤ sg) : MatchesTable g.paired.summary row ∧ RoundsTo (pairedT (realScores g.gain)) t := by
  obtain ⟨s,q,u,v,k,l⟩ := moments
  obtain ⟨c₁,c₂,c₃,c₄,c₅,c₆,c₇⟩ := check
  have eq : pairedT (realScores g.gain)^2 = ((sg:ℝ)/42)^2*42/(momentSS sg qg/41) := by
    rw [pairedT_sq_of_moments,k,l]
  have hp : 0 ≤ pairedT (realScores g.gain) := by
    rw [pairedT,mean_integer,k]
    exact div_nonneg (mul_nonneg (div_nonneg (by exact_mod_cast pos) (by norm_num)) (sqrt_nonneg _)) (sqrt_nonneg _)
  rw [← eq,sqrt_sq hp] at c₇
  refine ⟨?_,c₇⟩
  constructor <;> dsimp only [PairedGroup.summary] <;>
    (try rw [gain_cast]) <;>
    simp only [IntegerPair.paired,mean_integer,sampleSD,ss_integer,s,q,u,v,k,l] <;> assumption

private def ControlMoments (g : IntegerPair) : Prop := total g.pre = 114 ∧ squareTotal g.pre = 526 ∧
  total g.post = 347 ∧ squareTotal g.post = 3205 ∧ total g.gain = 233 ∧ squareTotal g.gain = 1831
private def PuzzleMoments (g : IntegerPair) : Prop := total g.pre = 158 ∧ squareTotal g.pre = 790 ∧
  total g.post = 389 ∧ squareTotal g.post = 3891 ∧ total g.gain = 231 ∧ squareTotal g.gain = 1795

private theorem compatible (a b : IntegerPair) (ma : ControlMoments a) (mb : PuzzleMoments b)
    (extra : ceilingCount a.post = 5 ∧ ceilingCount b.post = 9 ∧ OnThinkingScale a ∧ OnThinkingScale b) :
    MatchesThinkingReport a b := by
  obtain ⟨ta,pa⟩ := table_and_t a thinkingControl 9.92 _ _ _ _ _ _ ma (by
    dsimp [thinkingControl]; refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    all_goals first | (apply roundSqrt <;> norm_num [momentSS]) | norm_num [RoundsTo,abs_le]) (by decide)
  obtain ⟨tb,pb⟩ := table_and_t b thinkingPuzzles 9.97 _ _ _ _ _ _ mb (by
    dsimp [thinkingPuzzles]; refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    all_goals first | (apply roundSqrt <;> norm_num [momentSS]) | norm_num [RoundsTo,abs_le]) (by decide)
  exact ⟨ta,tb,pa,pb,extra⟩

/- Finite witnesses of non-identification, not observations. Both assignments
use the same 84 bounded integer pairs. Only the first four pairs of each
group exchange labels. At their common baseline 2, {7,9,9,9} and {8,8,8,10}
have the same sum and the same sum of squares. -/
private def referenceRows (arm : Bool) : Array (ℤ × ℤ) :=
  if arm then
    #[(2,8),(2,8),(2,8),(2,10),(0,10),(0,10),(1,11),
      (3,9),(3,9),(3,9),(3,9),(3,9),(3,9),(3,9),
      (3,9),(3,9),(3,9),(3,9),(3,9),(3,9),(3,9),
      (3,9),(3,9),(3,9),(3,9),(3,9),(3,11),(3,11),
      (3,11),(4,4),(4,12),(4,12),(4,12),(5,8),(7,12),
      (7,12),(7,12),(7,12),(8,0),(8,0),(9,12),(9,12)]
  else
    #[(2,7),(2,9),(2,9),(2,9),(1,2),(1,9),(1,9),
      (1,9),(1,9),(1,9),(1,9),(1,9),(1,9),(1,9),
      (1,9),(1,9),(1,9),(1,9),(1,9),(1,9),(1,9),
      (1,10),(1,10),(1,10),(2,4),(3,6),(3,8),(3,11),
      (3,11),(4,1),(4,1),(4,8),(4,8),(4,12),(4,12),
      (5,4),(5,4),(5,8),(6,3),(9,12),(9,12),(9,12)]

private def assignedArm (swap arm : Bool) (i : Fin 42) : Bool :=
  if swap && i.val < 4 then !arm else arm

private def assignment (swap arm : Bool) : IntegerPair :=
  let obs := fun i : Fin 42 => (referenceRows (assignedArm swap arm i))[i.val]!
  ⟨fun i => (obs i).1,fun i => (obs i).2⟩

private theorem reports (swap : Bool) :
    MatchesThinkingReport (assignment swap false) (assignment swap true) := by
  apply compatible
  · unfold ControlMoments
    cases swap <;> decide +kernel
  · unfold PuzzleMoments
    cases swap <;> decide +kernel
  · unfold OnThinkingScale
    cases swap <;> decide +kernel

/-- Two admissible studies give different post-test U statistics despite
the same published parametric inputs and ceiling counts. -/
theorem thinking_post_ranks_not_determined :
    ∃ a b c d : IntegerPair, MatchesThinkingReport a b ∧ MatchesThinkingReport c d ∧
      twiceU a.post b.post = 2154 ∧ twiceU c.post d.post = 2193 := by
  exact ⟨_,_,_,_,reports false,reports true,by decide +kernel,by decide +kernel⟩

/-- Pool two score columns, counting every pupil separately. -/
def poolColumns (a b : IntegerScores) (i : Fin 84) : ℤ :=
  if h : i.val < 42 then a ⟨i.val,h⟩ else b ⟨i.val-42,by omega⟩

def pooledPost (a b : IntegerPair) := poolColumns a.post b.post

def postRankP (a b : IntegerPair) : ℚ :=
  rankPermutationP (pooledPost a b) 42 (twiceU a.post b.post)

/-- Multiplicities and encoded midranks of the common pooled post-test distribution. -/
private def pooledWeights : List ℕ :=
  ([(2,8195), (2,8199), (1,8202), (1,8204), (4,8209), (1,8214), (1,8216), (8,8225), (38,8271), (6,8315), (6,8327), (14,8347)] : List (ℕ × ℕ)).flatMap
    (fun block => List.replicate block.1 block.2)

private theorem packed_example (swap : Bool) :
    packedWeights pooledWeights = packedWeights ((List.finRange 84).map
      (rankWeight (pooledPost (assignment swap false) (assignment swap true)))) := by
  let xs := (List.finRange 84).map (rankWeight (pooledPost (assignment swap false) (assignment swap true)))
  have perm : List.Perm pooledWeights xs := by cases swap <;> decide +kernel
  rw [packedWeights_eq,packedWeights_eq]
  exact (perm.map _).prod_eq

/-- With the exact balanced-label permutation reference and the usual
two-sided distance from the null center, reports matching all the stated
constraints can even fall on opposite sides of the 5% threshold. -/
theorem thinking_post_rank_decision_not_determined :
    ∃ a b c d : IntegerPair, MatchesThinkingReport a b ∧ MatchesThinkingReport c d ∧
      0.0662606 < postRankP a b ∧ postRankP a b < 0.0662607 ∧
      0.0430124 < postRankP c d ∧ postRankP c d < 0.0430125 := by
  let a := assignment false false
  let b := assignment false true
  let c := assignment true false
  let d := assignment true true
  have p₁ := rankPermutation_count (pooledPost a b) 390 347244 348023
    8887574151686823067164471 10455238962147243728134345 (packedWeights pooledWeights)
    (by decide) (by decide) (by decide) (by decide) (packed_example false) (by decide +kernel) (by decide +kernel)
  have p₂ := rankPermutation_count (pooledPost c d) 429 347205 348062
    8868058312946478122026934 10474754800887588673271882 (packedWeights pooledWeights)
    (by decide) (by decide) (by decide) (by decide) (packed_example true) (by decide +kernel) (by decide +kernel)
  have u₁ : twiceU a.post b.post = 1764+390 := by decide +kernel
  have u₂ : twiceU c.post d.post = 1764+429 := by decide +kernel
  refine ⟨a,b,c,d,reports false,reports true,?_⟩
  simp only [postRankP,u₁,u₂,p₁,p₂]
  decide +kernel

def gainRankP (a b : IntegerPair) : ℚ :=
  rankPermutationP (poolColumns a.gain b.gain) 42 (twiceU a.gain b.gain)

private def gainWeights : List ℕ :=
  ([(2,8195),(3,8200),(2,8205),(1,8208),(1,8210),(1,8212),(8,8221),(2,8231),
    (6,8239),(22,8267),(3,8292),(27,8322),(3,8352),(3,8358)] : List (ℕ × ℕ)).flatMap
    (fun block => List.replicate block.1 block.2)

private theorem packed_gains (swap : Bool) :
    packedWeights gainWeights = packedWeights ((List.finRange 84).map
      (rankWeight (poolColumns (assignment swap false).gain (assignment swap true).gain))) := by
  let xs := (List.finRange 84).map (rankWeight (poolColumns (assignment swap false).gain (assignment swap true).gain))
  have perm : List.Perm gainWeights xs := by cases swap <;> decide +kernel
  rw [packedWeights_eq,packedWeights_eq]
  exact (perm.map _).prod_eq

/-- The same published paired summaries and ceiling counts also leave the
exact rank probability for the change scores undetermined. -/
theorem thinking_gain_rank_probability_not_determined :
    ∃ a b c d : IntegerPair, MatchesThinkingReport a b ∧ MatchesThinkingReport c d ∧
      0.32606 < gainRankP a b ∧ gainRankP a b < 0.32607 ∧
      0.30828 < gainRankP c d ∧ gainRankP c d < 0.30829 := by
  let a := assignment false false
  let b := assignment false true
  let c := assignment true false
  let d := assignment true true
  have p₁ := rankPermutation_count (poolColumns a.gain b.gain) 215 347419 347848
    9105669395446119250901617 10237143718387947544397199 (packedWeights gainWeights)
    (by decide) (by decide) (by decide) (by decide) (packed_gains false) (by decide +kernel) (by decide +kernel)
  have p₂ := rankPermutation_count (poolColumns c.gain d.gain) 223 347411 347856
    9090738927740698414618779 10252074186093368380680037 (packedWeights gainWeights)
    (by decide) (by decide) (by decide) (by decide) (packed_gains true) (by decide +kernel) (by decide +kernel)
  have eq (s : Fin 84 → ℤ) {x y : ℕ} (h : Nat.dist x (42*42) = Nat.dist y (42*42)) :
      rankPermutationP s 42 x = rankPermutationP s 42 y := by simp only [rankPermutationP,h]
  have e₁ : gainRankP a b = rankPermutationP (poolColumns a.gain b.gain) 42 (1764+215) :=
    eq _ (x:=twiceU a.gain b.gain) (by decide +kernel)
  have e₂ : gainRankP c d = rankPermutationP (poolColumns c.gain d.gain) 42 (1764+223) :=
    eq _ (x:=twiceU c.gain d.gain) (by decide +kernel)
  refine ⟨a,b,c,d,reports false,reports true,?_⟩
  simp only [e₁,e₂,p₁,p₂]
  decide +kernel

end Thesis.StudyANCOVA
