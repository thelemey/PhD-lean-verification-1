import Thesis.WelchRounding
import Thesis.ThinkingWelch

open Real

namespace Thesis.StudyANCOVA

private theorem pre_bounds {a b : ℝ} (ha : RoundsTo a 24.68) (hb : RoundsTo b 22.11) :
    Bounds (welchDF a b) 81.01 81.04 ∧ Bounds (welchSE a b) 5.11181 5.114 :=
  welch_df_se_bounds 24.68 22.11 ha hb (by decide +kernel) (by decide +kernel) (by decide +kernel)
    _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem post_bounds {a b : ℝ} (ha : RoundsTo a 21.61) (hb : RoundsTo b 20.19) :
    Bounds (welchDF a b) 81.61 81.64 ∧ Bounds (welchSE a b) 4.56229 4.56448 :=
  welch_df_se_bounds 21.61 20.19 ha hb (by decide +kernel) (by decide +kernel) (by decide +kernel)
    _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem gain_bounds {a b : ℝ} (ha : RoundsTo a 21.08) (hb : RoundsTo b 19.50) :
    Bounds (welchDF a b) 81.49 81.52 ∧ Bounds (welchSE a b) 4.42990 4.43209 :=
  welch_df_se_bounds 21.08 19.50 ha hb (by decide +kernel) (by decide +kernel) (by decide +kernel)
    _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Unadjusted comparisons for the hundred-point instrument, before and
after instruction. In particular the one-sided p rounds to the MINITAB
value 0.004 and the two-sided result is significant at 1%. -/
theorem numbers_welch_probabilities (A B : PairedGroup)
    (hA : MatchesTable A.summary numbersControl) (hB : MatchesTable B.summary numbersPuzzles) :
    let a := A.summary
    let b := B.summary
    let p := welchP (b.post-a.post) a.postSD b.postSD
    Bounds (welchP (b.pre-a.pre) a.preSD b.preSD) 0.02177 0.02208 ∧
    Bounds p 0.00763 0.00778 ∧ |p/2-0.004| ≤ 1/2000 := by
  intro a b p
  obtain ⟨dx,dy,_,_⟩ := numbers_mean_contrasts a b hA hB A.summary_gain B.summary_gain
  obtain ⟨dp,sp⟩ := pre_bounds hA.preSD hB.preSD
  obtain ⟨dq,sq⟩ := post_bounds hA.postSD hB.postSD
  have tp := (dx.div sp (by decide +kernel) (by decide +kernel)).widen (l:=2.3347) (u:=2.3388)
    (by decide +kernel) (by decide +kernel)
  have tq := (dy.div sq (by decide +kernel) (by decide +kernel)).widen (l:=2.7308) (u:=2.7355)
    (by decide +kernel) (by decide +kernel)
  have pre := large_welch_box dp tp (x:=0.261027) (y:=0.258278)
    (l₁:=0.02206) (u₁:=0.02208) (l₂:=0.02177) (u₂:=0.02179)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0.2525645 0.2525646 0.2500718 0.2500719 (by decide +kernel) (by decide +kernel)
  have post := large_welch_box dq tq (x:=0.305312) (y:=0.302086)
    (l₁:=0.00776) (u₁:=0.00778) (l₂:=0.00763) (u₂:=0.00764)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0.2920054 0.2920055 0.2891793 0.2891794 (by decide +kernel) (by decide +kernel)
  have hp : Bounds p 0.00763 0.00778 := by
    dsimp only [p]
    rw [welchP_eq_of_positive ((by norm_num : (0:ℝ) ≤ (12.465:ℚ)).trans dy.lower)]
    exact post
  refine ⟨?_,hp,?_⟩
  · rw [welchP_eq_of_positive ((by norm_num : (0:ℝ) ≤ (11.940:ℚ)).trans dx.lower)]
    exact pre
  · obtain ⟨l,u⟩ := hp
    simp only [Rat.cast_ofScientific] at l u
    exact abs_le.2 ⟨by linarith only [l],by linarith only [u]⟩

/-- Both displayed degrees of freedom and standardized differences survive
rounding of the descriptive table, independently of the reported p values. -/
theorem numbers_welch_effect_sizes (A B : PairedGroup)
    (hA : MatchesTable A.summary numbersControl) (hB : MatchesTable B.summary numbersPuzzles) :
    let a := A.summary
    let b := B.summary
    |welchDF a.preSD b.preSD-81.0| ≤ 1/20 ∧ |welchDF a.postSD b.postSD-81.6| ≤ 1/20 ∧
    RoundsTo (pooledCohenD (b.pre-a.pre) (withinSS a.preSD b.preSD)) 0.51 ∧
    RoundsTo (pooledCohenD (b.post-a.post) (withinSS a.postSD b.postSD)) 0.60 := by
  intro a b
  obtain ⟨dx,dy,_,_⟩ := numbers_mean_contrasts a b hA hB A.summary_gain B.summary_gain
  obtain ⟨⟨pl,pu⟩,_⟩ := pre_bounds hA.preSD hB.preSD
  obtain ⟨⟨ql,qu⟩,_⟩ := post_bounds hA.postSD hB.postSD
  have X := pooled_bounds 24.68 22.11 hA.preSD hB.preSD (by decide +kernel) (by decide +kernel)
  have Y := pooled_bounds 21.61 20.19 hA.postSD hB.postSD (by decide +kernel) (by decide +kernel)
  have sp := (X.div (Bounds.exactValue 82) (by decide +kernel) (by decide +kernel)).sqrt
    23.42 23.44 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have sq := (Y.div (Bounds.exactValue 82) (by decide +kernel) (by decide +kernel)).sqrt
    20.90 20.92 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_ofScientific] at pl pu ql qu
  exact ⟨abs_le.2 ⟨by linarith only [pl],by linarith only [pu]⟩,
    abs_le.2 ⟨by linarith only [ql],by linarith only [qu]⟩,
    (dx.div sp (by decide +kernel) (by decide +kernel)).rounds 0.51 (by decide +kernel) (by decide +kernel),
    (dy.div sq (by decide +kernel) (by decide +kernel)).rounds 0.60 (by decide +kernel) (by decide +kernel)⟩

/-- The source reports a gain difference of 0.52 in addition to rounding
the two group means separately. Its extra digit narrows the gain p to the
published 0.91, while the decision already follows from the table alone. -/
theorem numbers_welch_gains (A B : PairedGroup)
    (hA : MatchesTable A.summary numbersControl) (hB : MatchesTable B.summary numbersPuzzles) :
    let a := A.summary
    let b := B.summary
    let p := welchP (b.gain-a.gain) a.gainSD b.gainSD
    Bounds p 0.9029 0.9079 ∧ (RoundsTo (b.gain-a.gain) 0.52 → RoundsTo p 0.91) := by
  intro a b p
  obtain ⟨_,_,dg,_⟩ := numbers_mean_contrasts a b hA hB A.summary_gain B.summary_gain
  obtain ⟨df,se⟩ := gain_bounds hA.gainSD hB.gainSD
  have h := (dg.div se (by decide +kernel) (by decide +kernel)).widen (l:=0.1173) (u:=0.12191)
    (by decide +kernel) (by decide +kernel)
  have hp : p = studentTwoSidedP (welchDF a.gainSD b.gainSD) ((b.gain-a.gain)/welchSE a.gainSD b.gainSD) :=
    welchP_eq_of_positive ((by norm_num : (0:ℝ) ≤ (0.520:ℚ)).trans dg.lower)
  rw [hp]
  constructor
  · exact small_welch_box df h (x:=0.012991) (y:=0.013505)
      (l₁:=0.9077) (u₁:=0.9079) (l₂:=0.9029) (u₂:=0.9031)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) 0.0129899 0.0129900 0.0135037 0.0135038 (by decide +kernel) (by decide +kernel)
  · intro cd
    have dg' : Bounds (b.gain-a.gain) 0.520 0.525 :=
      ⟨dg.lower,by have := (abs_le.mp cd).2; simp only [Rat.cast_ofScientific]; linarith only [this]⟩
    have h' := (dg'.div se (by decide +kernel) (by decide +kernel)).widen (l:=0.1173) (u:=0.11853)
      (by decide +kernel) (by decide +kernel)
    have out := small_welch_box df h' (x:=0.012991) (y:=0.013131)
      (l₁:=0.9077) (u₁:=0.9079) (l₂:=0.9056) (u₂:=0.9057)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) 0.0129899 0.0129900 0.0131298 0.0131299 (by decide +kernel) (by decide +kernel)
    exact out.rounds 0.91 (by decide +kernel) (by decide +kernel)

/-- Ranges for both endpoints of a genuine 95% interval: c is the
critical value of the Student distribution at the actual fractional df. -/
def WelchIntervalBounds (d se v : ℝ) (ll lu ul uu : ℚ) : Prop :=
  ∃ c, 0 ≤ c ∧ studentTwoSidedP v c = 0.05 ∧ Bounds (d-c*se) ll lu ∧ Bounds (d+c*se) ul uu

private theorem welch_limits {d se v : ℝ} {dl du sl su vl vu ll lu ul uu : ℚ}
    (diff : Bounds d dl du) (err : Bounds se sl su) (df : Bounds v vl vu)
    (left : 81 ≤ vl) (right : vu ≤ 83) (spos : 0 ≤ sl)
    (l₁ : ll ≤ dl-1.991*su) (l₂ : du-1.988*sl ≤ lu)
    (u₁ : ul ≤ dl+1.988*sl) (u₂ : du+1.991*su ≤ uu) : WelchIntervalBounds d se v ll lu ul uu := by
  obtain ⟨v₁,v₂⟩ := df.widen left right
  obtain ⟨c,hc,he,_⟩ := welch_critical95_bounds (by exact_mod_cast v₁) (by exact_mod_cast v₂)
  have cb : Bounds c 1.988 1.991 := ⟨by exact_mod_cast hc.1,by exact_mod_cast hc.2⟩
  have w := cb.mul err (by decide +kernel) spos
  exact ⟨c,(by norm_num : (0:ℝ) ≤ 1.988).trans hc.1,he,(diff.sub w).widen l₁ l₂,(diff.add w).widen u₁ u₂⟩

/-- Independent enclosures for all three 95% intervals on the hundred-point
scale. Both baseline and post-test exclude zero, while the gain comparison
contains zero. The hundredths of the original endpoints use more precision
than the two-decimal means and SDs. -/
theorem numbers_welch_intervals (A B : PairedGroup)
    (hA : MatchesTable A.summary numbersControl) (hB : MatchesTable B.summary numbersPuzzles) :
    let a := A.summary
    let b := B.summary
    WelchIntervalBounds (b.pre-a.pre) (welchSE a.preSD b.preSD) (welchDF a.preSD b.preSD)
      1.7580 1.7928 22.1022 22.1370 ∧
    WelchIntervalBounds (b.post-a.post) (welchSE a.postSD b.postSD) (welchDF a.postSD b.postSD)
      3.3771 3.4102 21.5348 21.5679 ∧
    WelchIntervalBounds (b.gain-a.gain) (welchSE a.gainSD b.gainSD) (welchDF a.gainSD b.gainSD)
      (-8.3043) (-8.2666) 9.3266 9.3643 := by
  obtain ⟨x,y,g,_⟩ := numbers_mean_contrasts A.summary B.summary hA hB A.summary_gain B.summary_gain
  obtain ⟨vx,sx⟩ := pre_bounds hA.preSD hB.preSD
  obtain ⟨vy,sy⟩ := post_bounds hA.postSD hB.postSD
  obtain ⟨vg,sg⟩ := gain_bounds hA.gainSD hB.gainSD
  refine ⟨welch_limits x sx vx ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    welch_limits y sy vy ?_ ?_ ?_ ?_ ?_ ?_ ?_,welch_limits g sg vg ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> decide +kernel

end Thesis.StudyANCOVA
