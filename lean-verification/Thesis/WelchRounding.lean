import Thesis.NumbersANCOVA
import Thesis.StudentScaledReference

open Real Set

namespace Thesis.StudyANCOVA

/-- For equal sample sizes, the degrees of freedom depend only on the
relative imbalance of the two variances. -/
theorem welchDF_eq_imbalance {a b : ℝ} (ha : 0 < a) :
    welchDF a b = 82/(1+((a^2-b^2)/(a^2+b^2))^2) := by
  have s : 0 < a^2+b^2 := add_pos_of_pos_of_nonneg (by positivity) (sq_nonneg _)
  have q : 0 < a^4+b^4 := add_pos_of_pos_of_nonneg (by positivity) (by positivity)
  unfold welchDF
  field_simp
  ring

noncomputable def welchSE (a b : ℝ) := sqrt ((a^2+b^2)/42)

theorem welchP_eq_of_positive {d a b : ℝ} (hd : 0 ≤ d) :
    welchP d a b = studentTwoSidedP (welchDF a b) (d/welchSE a b) := by
  unfold welchP welchSquared withinSS welchSE
  rw [sqrt_div (sq_nonneg _),sqrt_sq hd]
  congr 3
  ring

/-- Each endpoint is obtained from the standard deviations as published,
including their independent rounding errors. -/
theorem welch_df_se_bounds {a b : ℝ} (a₀ b₀ : ℚ)
    (ha : RoundsTo a (a₀:ℝ)) (hb : RoundsTo b (b₀:ℝ))
    (ap : 0 < a₀-1/200) (bp : 0 ≤ b₀-1/200)
    (gap : 0 ≤ (a₀-1/200)^2-(b₀+1/200)^2)
    (dfL dfU seL seU : ℚ)
    (dflo : dfL ≤ 82/(1+(((a₀+1/200)^2-(b₀-1/200)^2)/((a₀-1/200)^2+(b₀-1/200)^2))^2))
    (dfhi : 82/(1+(((a₀-1/200)^2-(b₀+1/200)^2)/((a₀+1/200)^2+(b₀+1/200)^2))^2) ≤ dfU)
    (selo : seL^2 ≤ ((a₀-1/200)^2+(b₀-1/200)^2)/42)
    (sehi : ((a₀+1/200)^2+(b₀+1/200)^2)/42 ≤ seU^2) (sepos : 0 ≤ seU) :
    Bounds (welchDF a b) dfL dfU ∧ Bounds (welchSE a b) seL seU := by
  have ar := Bounds.of_rounding a₀ ha
  have br := Bounds.of_rounding b₀ hb
  have aa := ar.sq ap.le
  have bb := br.sq bp
  have sum := aa.add bb
  have sp : 0 < (a₀-1/200)^2+(b₀-1/200)^2 := by positivity
  have rr := (aa.sub bb).div sum gap sp
  have z := rr.sq (div_nonneg gap (lt_of_lt_of_le sp (by
    linarith only [pow_le_pow_left₀ ap.le (show a₀-1/200 ≤ a₀+1/200 by linarith) 2,
      pow_le_pow_left₀ bp (show b₀-1/200 ≤ b₀+1/200 by linarith) 2])).le)
  have one := (Bounds.exactValue 1).add z
  have df := ((Bounds.exactValue 82).div one (by decide +kernel) (by positivity)).widen dflo dfhi
  have aPos : 0 < a := (show (0:ℝ) < ((a₀-1/200:ℚ):ℝ) by exact_mod_cast ap).trans_le ar.lower
  have v := sum.div (Bounds.exactValue 42) sp.le (by decide +kernel)
  constructor
  · rw [welchDF_eq_imbalance aPos]
    simpa only [Rat.cast_ofNat,Rat.cast_one] using df
  · simpa only [welchSE,Rat.cast_ofNat] using v.sqrt seL seU selo sehi sepos

/-- Bound the ordinary (unscaled) test using the even-degree reference
laws at 80 and 82 for the two larger statistics. -/
theorem welch_large_reference {v t : ℝ} {x y l u : ℝ} (hv : 80 ≤ v) (hv' : v ≤ 82)
    (ht : 1.5 ≤ t) (hx : 0 ≤ x) (hy : 0 ≤ y) (xl : 80*x^2 ≤ t^2) (yu : t^2 ≤ 82*y^2)
    (pl : l ≤ studentTwoSidedP 82 (sqrt 82*y)) (pu : studentTwoSidedP 80 (sqrt 80*x) ≤ u) :
    l ≤ studentTwoSidedP v t ∧ studentTwoSidedP v t ≤ u := by
  have tp : 0 ≤ t := by linarith
  have sl : sqrt 80*x ≤ t := by
    have h : (sqrt 80*x)^2 ≤ t^2 := by simpa only [mul_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 80)] using xl
    nlinarith only [h,tp]
  have su : t ≤ sqrt 82*y := by
    have h : t^2 ≤ (sqrt 82*y)^2 := by simpa only [mul_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 82)] using yu
    nlinarith only [h,mul_nonneg (sqrt_nonneg 82) hy]
  have l₁ := (studentProbability_strictAnti (v:=82) (by norm_num)).antitoneOn tp (mul_nonneg (sqrt_nonneg _) hy) su
  have u₁ := (studentProbability_strictAnti (v:=80) (by norm_num)).antitoneOn (mul_nonneg (sqrt_nonneg _) hx) tp sl
  exact ⟨pl.trans (l₁.trans (student_probability_antitone_degrees (by linarith) hv' ht)),
    (student_probability_antitone_degrees (by norm_num) hv ht).trans (u₁.trans pu)⟩

/-- For gains the signed statistic is small. Compare on a common scaled
axis before taking the ratio of the Student tail to its total mass. -/
theorem welch_small_reference {v t x y l u : ℝ} (hv : 80 ≤ v) (hv' : v ≤ 82) (ht : 0 < t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (xl : v*x^2 ≤ t^2) (yu : t^2 ≤ v*y^2)
    (pl : l ≤ studentTwoSidedP 82 (sqrt 82*y)) (pu : studentTwoSidedP 80 (sqrt 80*x) ≤ u) :
    l ≤ studentTwoSidedP v t ∧ studentTwoSidedP v t ≤ u := by
  have vp : 0 < v := by linarith
  let w := t / sqrt v
  have wp : 0 < w := div_pos ht (sqrt_pos.2 vp)
  have ww : sqrt v*w=t := mul_div_cancel₀ t (sqrt_pos.2 vp).ne'
  have wl : x ≤ w := by
    apply (le_div_iff₀ (sqrt_pos.2 vp)).2
    have h : (x*sqrt v)^2 ≤ t^2 := by rw [mul_pow,sq_sqrt vp.le,mul_comm]; exact xl
    nlinarith only [h,ht]
  have wu : w ≤ y := by
    apply (div_le_iff₀ (sqrt_pos.2 vp)).2
    have h : t^2 ≤ (y*sqrt v)^2 := by rw [mul_pow,sq_sqrt vp.le,mul_comm]; exact yu
    nlinarith only [h,mul_nonneg hy (sqrt_nonneg v)]
  have ll := (studentProbability_strictAnti (v:=82) (by norm_num)).antitoneOn
    (mul_nonneg (sqrt_nonneg _) wp.le) (mul_nonneg (sqrt_nonneg _) hy) (mul_le_mul_of_nonneg_left wu (sqrt_nonneg 82))
  have uu := (studentProbability_strictAnti (v:=80) (by norm_num)).antitoneOn
    (mul_nonneg (sqrt_nonneg _) hx) (mul_nonneg (sqrt_nonneg _) wp.le) (mul_le_mul_of_nonneg_left wl (sqrt_nonneg 80))
  rw [← ww]
  exact ⟨pl.trans (ll.trans (student_scaled_probability_antitone (by linarith) hv' wp)),
    (student_scaled_probability_antitone (by norm_num) hv wp).trans (uu.trans pu)⟩


private theorem even80 (z y₁ y₂ l u : ℚ) (h : EvenReferenceCertificate 39 z y₁ y₂ l u) :
    Bounds (studentTwoSidedP 80 (sqrt 80*(z:ℝ))) l u := by
  have ref := even_reference_scaled 39 (d := sqrt 80) (by positivity) (by norm_num) z y₁ y₂ l u h
  simp only [Nat.cast_ofNat,show (2*39+2:ℝ)=80 by norm_num] at ref
  exact ⟨ref.1,ref.2⟩

private theorem even82 (z y₁ y₂ l u : ℚ) (h : EvenReferenceCertificate 40 z y₁ y₂ l u) :
    Bounds (studentTwoSidedP 82 (sqrt 82*(z:ℝ))) l u := by
  have ref := even_reference_scaled 40 (d := sqrt 82) (by positivity) (by norm_num) z y₁ y₂ l u h
  simp only [Nat.cast_ofNat,show (2*40+2:ℝ)=82 by norm_num] at ref
  exact ⟨ref.1,ref.2⟩

/-- For fixed ordinary t, use the independent bounds in degrees and in t. -/
theorem large_welch_box {v t : ℝ} {vl vu tl tu x y l₁ u₁ l₂ u₂ : ℚ}
    (hv : Bounds v vl vu) (ht : Bounds t tl tu) (v₀ : 80 ≤ vl) (v₁ : vu ≤ 82)
    (t₀ : 1.5 ≤ tl) (xl : 0 ≤ x) (yl : 0 ≤ y)
    (hx : 80*x^2 ≤ tl^2) (hy : tu^2 ≤ 82*y^2)
    (x₁ x₂ y₁ y₂ : ℚ) (lower : EvenReferenceCertificate 40 y y₁ y₂ l₂ u₂)
    (upper : EvenReferenceCertificate 39 x x₁ x₂ l₁ u₁) :
    Bounds (studentTwoSidedP v t) l₂ u₁ := by
  obtain ⟨vl',vu'⟩ := hv.widen v₀ v₁
  have t0 := (ht.widen t₀ le_rfl).lower
  have ts := ht.sq (by linarith : 0 ≤ tl)
  have q := welch_large_reference (by exact_mod_cast vl') (by exact_mod_cast vu') (by exact_mod_cast t0)
    (show 0 ≤ (x:ℝ) by exact_mod_cast xl) (show 0 ≤ (y:ℝ) by exact_mod_cast yl)
    (show 80*(x:ℝ)^2 ≤ t^2 by exact_mod_cast (ts.widen hx le_rfl).lower)
    (show t^2 ≤ 82*(y:ℝ)^2 by exact_mod_cast (ts.widen le_rfl hy).upper)
    (even82 _ _ _ _ _ lower).lower (even80 _ _ _ _ _ upper).upper
  exact ⟨q.1,q.2⟩

/-- The corresponding small-t certificate works at fixed t/√ν. -/
theorem small_welch_box {v t : ℝ} {vl vu tl tu x y l₁ u₁ l₂ u₂ : ℚ}
    (hv : Bounds v vl vu) (ht : Bounds t tl tu) (v₀ : 80 ≤ vl) (v₁ : vu ≤ 82)
    (t₀ : 0 < tl) (xl : 0 ≤ x) (yl : 0 ≤ y)
    (hx : vu*x^2 ≤ tl^2) (hy : tu^2 ≤ vl*y^2)
    (x₁ x₂ y₁ y₂ : ℚ) (lower : EvenReferenceCertificate 40 y y₁ y₂ l₂ u₂)
    (upper : EvenReferenceCertificate 39 x x₁ x₂ l₁ u₁) :
    Bounds (studentTwoSidedP v t) l₂ u₁ := by
  obtain ⟨vl',vu'⟩ := hv.widen v₀ v₁
  have t0 := (show 0 < (tl:ℝ) by exact_mod_cast t₀).trans_le ht.lower
  have ts := ht.sq t₀.le
  have xl' := mul_le_mul_of_nonneg_right hv.upper (sq_nonneg (x:ℝ))
  have yu' := mul_le_mul_of_nonneg_right hv.lower (sq_nonneg (y:ℝ))
  have lo : (vu:ℝ)*(x:ℝ)^2 ≤ t^2 := by exact_mod_cast (ts.widen hx le_rfl).lower
  have hi : t^2 ≤ (vl:ℝ)*(y:ℝ)^2 := by exact_mod_cast (ts.widen le_rfl hy).upper
  have q := welch_small_reference (by exact_mod_cast vl') (by exact_mod_cast vu') t0
    (show 0 ≤ (x:ℝ) by exact_mod_cast xl) (show 0 ≤ (y:ℝ) by exact_mod_cast yl)
    (xl'.trans lo) (hi.trans yu') (even82 _ _ _ _ _ lower).lower (even80 _ _ _ _ _ upper).upper
  exact ⟨q.1,q.2⟩

end Thesis.StudyANCOVA
