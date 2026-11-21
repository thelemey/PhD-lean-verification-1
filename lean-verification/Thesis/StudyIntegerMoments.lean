import Thesis.StudySignificance

open scoped BigOperators

namespace Thesis.StudyANCOVA

/-- The twelve one-point questions of the thinking instrument give integer
scores. Integer gains may be negative. No integrality assumption is made
about the separate hundred-point instrument. -/
abbrev IntegerScores := Fin 42 → ℤ

def total (x : IntegerScores) : ℤ := ∑ i, x i
def squareTotal (x : IntegerScores) : ℤ := ∑ i, x i ^ 2
def realScores (x : IntegerScores) : Fin 42 → ℝ := fun i => x i

noncomputable def momentSS (s q : ℤ) : ℝ := (q : ℝ) - (s : ℝ)^2 / 42

theorem mean_integer (x : IntegerScores) : mean (realScores x) = (total x : ℝ) / 42 := by
  simp [mean, realScores, total]

theorem ss_integer (x : IntegerScores) : ss (realScores x) = momentSS (total x) (squareTotal x) := by
  have he (i : Fin 42) : centered (realScores x) i ^ 2 =
      (x i : ℝ)^2 - 2 * ((total x : ℝ)/42) * x i + ((total x : ℝ)/42)^2 := by
    rw [centered, mean_integer]
    dsimp [realScores]
    ring
  simp only [ss, he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold momentSS squareTotal total
  push_cast
  ring

theorem squareTotal_parity (x : IntegerScores) : squareTotal x % 2 = total x % 2 := by
  have he (i : Fin 42) : x i ^ 2 % 2 = x i % 2 := by
    rw [pow_two, Int.mul_emod]
    rcases Int.emod_two_eq_zero_or_one (x i) with h | h <;> simp [h]
  unfold squareTotal total
  rw [Finset.sum_int_mod _ 2 (fun i => x i ^ 2), Finset.sum_int_mod _ 2 x]
  simp only [he]

theorem sampleSD_sq (x : Fin 42 → ℝ) : sampleSD x ^ 2 = ss x / 41 := by
  unfold sampleSD
  apply Real.sq_sqrt
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem rounded_integer_moments {x : IntegerScores} {m s : ℝ} {S L U : ℤ}
    (hm : RoundsTo (mean (realScores x)) m) (hs : RoundsTo (sampleSD (realScores x)) s)
    (hs₀ : 1/200 ≤ s)
    (hm₁ : (S:ℝ)-1 < 42*(m-1/200)) (hm₂ : 42*(m+1/200) < (S:ℝ)+1)
    (hq₁ : (L:ℝ)-1 < (S:ℝ)^2/42 + 41*(s-1/200)^2)
    (hq₂ : (S:ℝ)^2/42 + 41*(s+1/200)^2 < (U:ℝ)+1) :
    total x = S ∧ L ≤ squareTotal x ∧ squareTotal x ≤ U ∧ squareTotal x % 2 = S % 2 := by
  rw [mean_integer] at hm
  obtain ⟨hml,hmu⟩ := abs_le.mp hm
  have h₁ : S-1 < total x := by exact_mod_cast (show (S:ℝ)-1 < total x by linarith)
  have h₂ : total x < S+1 := by exact_mod_cast (show (total x : ℝ) < (S:ℝ)+1 by linarith)
  have hS : total x = S := by omega
  obtain ⟨hsl,hsu⟩ := abs_le.mp hs
  have hl := pow_le_pow_left₀ (sub_nonneg.mpr hs₀) (by linarith : s-1/200 ≤ sampleSD (realScores x)) 2
  have hu := pow_le_pow_left₀ (Real.sqrt_nonneg _) (by linarith : sampleSD (realScores x) ≤ s+1/200) 2
  change sampleSD (realScores x)^2 ≤ _ at hu
  rw [sampleSD_sq, ss_integer, hS, momentSS] at hl hu
  have hL : L-1 < squareTotal x := by exact_mod_cast (show (L:ℝ)-1 < squareTotal x by linarith)
  have hU : squareTotal x < U+1 := by exact_mod_cast (show (squareTotal x:ℝ) < (U:ℝ)+1 by linarith)
  exact ⟨hS, by omega, by omega, (squareTotal_parity x).trans (hS ▸ rfl)⟩

structure IntegerPair where
  pre : IntegerScores
  post : IntegerScores

def IntegerPair.gain (g : IntegerPair) : IntegerScores := fun i => g.post i - g.pre i

def IntegerPair.paired (g : IntegerPair) : PairedGroup := ⟨realScores g.pre, realScores g.post⟩

theorem gain_cast (g : IntegerPair) :
    (fun i => g.paired.post i - g.paired.pre i) = realScores g.gain := by
  funext i
  simp [IntegerPair.paired, IntegerPair.gain, realScores]

/-- Exact totals and sums of squares forced by the descriptive table alone.
For each group two integer gain sums of squares are compatible with the
rounding bounds; this statement does not select an unobserved pairing. -/
theorem thinking_integer_moments (A B : IntegerPair)
    (hA : MatchesTable A.paired.summary thinkingControl)
    (hB : MatchesTable B.paired.summary thinkingPuzzles) :
    (total A.pre = 114 ∧ squareTotal A.pre = 526) ∧
    (total A.post = 347 ∧ squareTotal A.post = 3205) ∧
    (total A.gain = 233 ∧ (squareTotal A.gain = 1829 ∨ squareTotal A.gain = 1831)) ∧
    (total B.pre = 158 ∧ squareTotal B.pre = 790) ∧
    (total B.post = 389 ∧ squareTotal B.post = 3891) ∧
    (total B.gain = 231 ∧ (squareTotal B.gain = 1795 ∨ squareTotal B.gain = 1797)) := by
  have preA := rounded_integer_moments (x := A.pre) (S := 114) (L := 526) (U := 527)
    hA.pre hA.preSD (by norm_num [thinkingControl]) (by norm_num [thinkingControl])
    (by norm_num [thinkingControl]) (by norm_num [thinkingControl]) (by norm_num [thinkingControl])
  have postA := rounded_integer_moments (x := A.post) (S := 347) (L := 3204) (U := 3205)
    hA.post hA.postSD (by norm_num [thinkingControl]) (by norm_num [thinkingControl])
    (by norm_num [thinkingControl]) (by norm_num [thinkingControl]) (by norm_num [thinkingControl])
  have preB := rounded_integer_moments (x := B.pre) (S := 158) (L := 789) (U := 790)
    hB.pre hB.preSD (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles])
    (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles])
  have postB := rounded_integer_moments (x := B.post) (S := 389) (L := 3890) (U := 3891)
    hB.post hB.postSD (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles])
    (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles])
  have gain (g : IntegerPair) (p : GroupSummary) (h : MatchesTable g.paired.summary p) :
      RoundsTo (mean (realScores g.gain)) p.gain ∧ RoundsTo (sampleSD (realScores g.gain)) p.gainSD := by
    rw [← gain_cast]
    exact ⟨h.gain, h.gainSD⟩
  obtain ⟨ma,sa⟩ := gain A _ hA
  obtain ⟨mb,sb⟩ := gain B _ hB
  have gainA := rounded_integer_moments (x := A.gain) (S := 233) (L := 1829) (U := 1831)
    ma sa (by norm_num [thinkingControl]) (by norm_num [thinkingControl])
    (by norm_num [thinkingControl]) (by norm_num [thinkingControl]) (by norm_num [thinkingControl])
  have gainB := rounded_integer_moments (x := B.gain) (S := 231) (L := 1795) (U := 1797)
    mb sb (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles])
    (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles]) (by norm_num [thinkingPuzzles])
  omega

end Thesis.StudyANCOVA
