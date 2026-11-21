import Thesis.MBonacciClosureDensity
import Thesis.MBonacciValues
import Thesis.PalindromicDensityReal

open Filter Topology

namespace Thesis.MBonacci

/-- The density of the standard m-bonacci word in prop:mbonacci, with m = n + 2. -/
theorem standardWord_palindromicDensity (n : Nat) :
    palindromicDensity (standardWord n) = 1 / beta n :=
  palindromicDensity_eq_of_cut (one_div_nonneg.mpr (zero_lt_one.trans (beta_spec n).1).le)
    fun _ _ hq => standardWord_below_density_iff n hq

theorem standardWord_palindromicDensity_fibonacci :
    palindromicDensity (standardWord 0) = 1 / goldenRatio := by
  rw [standardWord_palindromicDensity, fibonacci_root_eq_goldenRatio]

theorem standardWord_palindromicDensity_tribonacci :
    (54365 : ℝ) / 100000 < palindromicDensity (standardWord 1) ∧
      palindromicDensity (standardWord 1) < 54375 / 100000 := by
  rw [standardWord_palindromicDensity]
  exact tribonacci_density_rounding

theorem standardWord_palindromicDensity_tetranacci :
    (51875 : ℝ) / 100000 < palindromicDensity (standardWord 2) ∧
      palindromicDensity (standardWord 2) < 51885 / 100000 := by
  rw [standardWord_palindromicDensity]
  exact tetranacci_density_rounding

theorem standardWord_palindromicDensity_strictAnti :
    StrictAnti (fun n => palindromicDensity (standardWord n)) := by
  simpa only [standardWord_palindromicDensity] using reciprocal_beta_strictAnti

theorem standardWord_palindromicDensity_tendsto_half :
    Tendsto (fun n => palindromicDensity (standardWord n)) atTop (𝓝 (1 / 2)) := by
  simpa only [standardWord_palindromicDensity] using reciprocal_beta_tendsto_half

end Thesis.MBonacci
