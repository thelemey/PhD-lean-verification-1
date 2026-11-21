import Thesis.StudentDegreesComparison
import Thesis.StudentEvenDegrees

open Real Set MeasureTheory intervalIntegral

namespace Thesis.StudyANCOVA

private noncomputable def scaledKernel (v x : ℝ) := studentKernel v (sqrt v*x)

private theorem scaled_kernel_power {v : ℝ} (hv : 0 < v) (x : ℝ) :
    scaledKernel v x = (1+x^2)^(-(v+1)/2 : ℝ) := by
  rw [scaledKernel,studentKernel,mul_pow,sq_sqrt hv.le,mul_div_cancel_left₀ _ hv.ne',
    neg_div,Real.rpow_neg (by positivity),one_div]

/-- At a fixed positive t/√ν the normalized two-sided Student probability
decreases with ν, even for very small t. This covers the two gain tests,
which are unsuited to a large-statistic tail estimate. -/
theorem student_scaled_probability_antitone {a b x : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hx : 0 < x) :
    studentTwoSidedP b (sqrt b*x) ≤ studentTwoSidedP a (sqrt a*x) := by
  have pa := zero_lt_one.trans_le ha
  have pb := pa.trans_le hab
  let k (z : ℝ) := (1+z^2)^((a-b)/2 : ℝ)
  have ratio (z : ℝ) : scaledKernel b z = k z*scaledKernel a z := by
    rw [scaled_kernel_power pa,scaled_kernel_power pb]
    dsimp only [k]
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  have anti {z w : ℝ} (hz : 0 ≤ z) (hzw : z ≤ w) : k w ≤ k z := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    linarith only [pow_le_pow_left₀ hz hzw 2]
  have intg (v : ℝ) (hv : 1 ≤ v) : Integrable (scaledKernel v) :=
    (integrable_studentKernel hv).comp_mul_left' (sqrt_pos.2 (zero_lt_one.trans_le hv)).ne'
  have cont (v : ℝ) (hv : 0 < v) : Continuous (scaledKernel v) :=
    (continuous_studentKernel hv).comp (continuous_const.mul continuous_id)
  have pos (v : ℝ) (hv : 0 < v) (z : ℝ) : 0 < scaledKernel v z := studentKernel_pos hv _
  have bounds := normalized_tail_compare (f := scaledKernel a) (g := scaledKernel b) (k := k x) hx
    (intg a ha) (intg b (ha.trans hab)) (cont a pa) (cont b pb) (pos a pa) (pos b pb)
    (fun z hz => (ratio z) ▸ mul_le_mul_of_nonneg_right (anti hz.1 hz.2) (pos a pa z).le)
    (fun z hz => (ratio z) ▸ mul_le_mul_of_nonneg_right (anti hx.le hz.le) (pos a pa z).le)
  have tail (v : ℝ) (hv : 0 < v) (w : ℝ) :
      (∫ z in Ioi w, scaledKernel v z) = (sqrt v)⁻¹*studentTail v (sqrt v*w) := by
    simpa only [scaledKernel,studentTail,smul_eq_mul] using integral_comp_mul_left_Ioi (studentKernel v) w (sqrt_pos.2 hv)
  simp only [tail a pa,tail b pb,mul_zero,mul_div_mul_left _ _ (inv_ne_zero (sqrt_pos.2 pa).ne'),
    mul_div_mul_left _ _ (inv_ne_zero (sqrt_pos.2 pb).ne')] at bounds
  simpa only [studentTwoSidedP,abs_of_nonneg (mul_nonneg (sqrt_nonneg _) hx.le)] using bounds

def EvenReferenceCertificate (n : ℕ) (z y₁ y₂ l u : ℚ) : Prop :=
  0 ≤ z ∧ 0 ≤ y₁ ∧ y₂ ≤ 1 ∧ y₁ ≤ y₂ ∧ y₁^2*(1+z^2) ≤ z^2 ∧ z^2 ≤ y₂^2*(1+z^2) ∧
    evenReduction y₂ n ≤ (1-l)*evenReduction 1 n ∧ (1-u)*evenReduction 1 n ≤ evenReduction y₁ n

instance (n : ℕ) (z y₁ y₂ l u : ℚ) : Decidable (EvenReferenceCertificate n z y₁ y₂ l u) := by
  unfold EvenReferenceCertificate
  infer_instance

/-- A rational certificate for an even-degree reference value at the scaled
argument z. The CDF reduces to a polynomial in z/√(1+z²); all four
enclosure comparisons below are rational. -/
theorem even_reference_scaled (n : ℕ) {d : ℝ} (hd : 0 < d) (hd₂ : d^2 = 2*n+2)
    (z y₁ y₂ l u : ℚ) (certificate : EvenReferenceCertificate n z y₁ y₂ l u) :
    (l:ℝ) ≤ studentTwoSidedP (2*n+2) (d*(z:ℝ)) ∧ studentTwoSidedP (2*n+2) (d*(z:ℝ)) ≤ (u:ℝ) := by
  obtain ⟨hz,hy₁,hy₂,horder,yl,yu,pl,pu⟩ := certificate
  let y := sin (arctan (z:ℝ))
  have hz' : 0 ≤ (z:ℝ) := by exact_mod_cast hz
  have hy : 0 ≤ y := by dsimp [y]; rw [sin_arctan]; positivity
  have ys : y^2 = (z:ℝ)^2/(1+(z:ℝ)^2) := by
    dsimp [y]
    rw [sin_arctan,div_pow,sq_sqrt (by positivity)]
  have hl : (y₁:ℝ)^2 ≤ y^2 := by
    rw [ys]
    exact (le_div_iff₀ (by positivity)).2 (by exact_mod_cast yl)
  have hu : y^2 ≤ (y₂:ℝ)^2 := by
    rw [ys]
    exact (div_le_iff₀ (by positivity)).2 (by exact_mod_cast yu)
  have ya : 0 ≤ (y₁:ℝ) := by exact_mod_cast hy₁
  have yb : (y₂:ℝ) ≤ 1 := by exact_mod_cast hy₂
  have yab : (y₁:ℝ) ≤ y₂ := by exact_mod_cast horder
  have ya' : (y₁:ℝ) ≤ y := by nlinarith only [hl,hy,ya]
  have yb' : y ≤ (y₂:ℝ) := by nlinarith only [hu,yab,ya]
  have ym : y ∈ Icc (-1:ℝ) 1 := ⟨by linarith,by linarith⟩
  have m₁ := evenReduction_mono n (show (y₁:ℝ) ∈ Icc (-1:ℝ) 1 from ⟨by linarith,by linarith⟩) ym ya'
  have m₂ := evenReduction_mono n ym (show (y₂:ℝ) ∈ Icc (-1:ℝ) 1 from ⟨by linarith,yb⟩) yb'
  have pos (k : ℕ) : 0 < evenReduction (1:ℝ) k := by
    induction k with
    | zero => norm_num [evenReduction]
    | succ k ih =>
      simp only [evenReduction,one_pow,sub_self,zero_pow (Nat.succ_ne_zero k),mul_zero,add_zero]
      positivity
  have lo := (Rat.cast_le (K:=ℝ)).2 pl
  have hi := (Rat.cast_le (K:=ℝ)).2 pu
  simp only [Rat.cast_mul,Rat.cast_sub,Rat.cast_one,ratCast_evenReduction] at lo hi
  have hp := studentTwoSidedP_even n hd hd₂ (d*(z:ℝ))
  rw [abs_of_nonneg (mul_nonneg hd.le hz'),mul_div_cancel_left₀ _ hd.ne'] at hp
  change studentTwoSidedP _ _ = 1-evenReduction y n/evenReduction 1 n at hp
  rw [hp]
  exact ⟨by linarith only [(div_le_iff₀ (pos n)).2 (m₂.trans lo)],
    by linarith only [(le_div_iff₀ (pos n)).2 (hi.trans m₁)]⟩

end Thesis.StudyANCOVA
