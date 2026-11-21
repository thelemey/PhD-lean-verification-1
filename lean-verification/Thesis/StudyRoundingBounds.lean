import Thesis.StudySignificance

namespace Thesis.StudyANCOVA

/-- A closed rational enclosure of an unrounded value. Endpoint calculations
stay in ℚ, while the sample moments and the test statistics are real. -/
structure Bounds (x : ℝ) (lo hi : ℚ) : Prop where
  lower : (lo : ℝ) ≤ x
  upper : x ≤ (hi : ℝ)

namespace Bounds

variable {x y : ℝ} {a b c d : ℚ}

theorem of_rounding (q : ℚ) (h : RoundsTo x (q : ℝ)) : Bounds x (q-1/200) (q+1/200) := by
  obtain ⟨l,u⟩ := abs_le.mp h
  constructor <;> push_cast <;> linarith

theorem exactValue (v : ℚ) : Bounds (v : ℝ) v v := ⟨le_rfl,le_rfl⟩

theorem widen (hx : Bounds x a b) {l u : ℚ} (hl : l ≤ a) (hu : b ≤ u) : Bounds x l u :=
  ⟨((Rat.cast_le (K := ℝ)).2 hl).trans hx.lower,hx.upper.trans ((Rat.cast_le (K := ℝ)).2 hu)⟩

theorem add (hx : Bounds x a b) (hy : Bounds y c d) : Bounds (x+y) (a+c) (b+d) := by
  constructor
  · simpa only [Rat.cast_add] using add_le_add hx.lower hy.lower
  · simpa only [Rat.cast_add] using add_le_add hx.upper hy.upper

theorem sub (hx : Bounds x a b) (hy : Bounds y c d) : Bounds (x-y) (a-d) (b-c) := by
  constructor
  · simpa only [Rat.cast_sub] using sub_le_sub hx.lower hy.upper
  · simpa only [Rat.cast_sub] using sub_le_sub hx.upper hy.lower

theorem scale (hx : Bounds x a b) (k : ℚ) (hk : 0 ≤ k) : Bounds ((k:ℝ)*x) (k*a) (k*b) := by
  have hk' : 0 ≤ (k:ℝ) := by exact_mod_cast hk
  constructor
  · simpa only [Rat.cast_mul] using mul_le_mul_of_nonneg_left hx.lower hk'
  · simpa only [Rat.cast_mul] using mul_le_mul_of_nonneg_left hx.upper hk'

theorem mul (hx : Bounds x a b) (hy : Bounds y c d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    Bounds (x*y) (a*c) (b*d) := by
  have ha' : 0 ≤ (a:ℝ) := by exact_mod_cast ha
  have hc' : 0 ≤ (c:ℝ) := by exact_mod_cast hc
  constructor
  · simpa only [Rat.cast_mul] using mul_le_mul hx.lower hy.lower hc' (ha'.trans hx.lower)
  · simpa only [Rat.cast_mul] using mul_le_mul hx.upper hy.upper (hc'.trans hy.lower)
      (ha'.trans (hx.lower.trans hx.upper))

theorem div (hx : Bounds x a b) (hy : Bounds y c d) (ha : 0 ≤ a) (hc : 0 < c) :
    Bounds (x/y) (a/d) (b/c) := by
  have ha' : 0 ≤ (a:ℝ) := by exact_mod_cast ha
  have hc' : 0 < (c:ℝ) := by exact_mod_cast hc
  have hp := hc'.trans_le hy.lower
  constructor
  · rw [Rat.cast_div]
    exact (div_le_div_of_nonneg_left ha' hp hy.upper).trans (div_le_div_of_nonneg_right hx.lower hp.le)
  · rw [Rat.cast_div]
    exact (div_le_div_of_nonneg_left (ha'.trans hx.lower) hc' hy.lower).trans
      (div_le_div_of_nonneg_right hx.upper hc'.le)

theorem sq (hx : Bounds x a b) (ha : 0 ≤ a) : Bounds (x^2) (a^2) (b^2) := by
  simpa only [pow_two] using hx.mul hx ha ha

theorem sqrt (hx : Bounds x a b) (l u : ℚ) (hl : l^2 ≤ a) (hu : b ≤ u^2) (hu' : 0 ≤ u) :
    Bounds (Real.sqrt x) l u := by
  have hl' : (l:ℝ)^2 ≤ a := by exact_mod_cast hl
  have hu₁ : (b:ℝ) ≤ (u:ℝ)^2 := by exact_mod_cast hu
  exact ⟨Real.le_sqrt_of_sq_le (hl'.trans hx.lower),
    Real.sqrt_le_iff.2 ⟨by exact_mod_cast hu',hx.upper.trans hu₁⟩⟩

theorem rounds (hx : Bounds x a b) (q : ℚ) (hl : q-1/200 ≤ a) (hu : b ≤ q+1/200) :
    RoundsTo x (q:ℝ) := by
  obtain ⟨l,u⟩ := hx.widen hl hu
  push_cast at l u
  exact abs_le.2 ⟨by linarith,by linarith⟩

end Bounds
end Thesis.StudyANCOVA
