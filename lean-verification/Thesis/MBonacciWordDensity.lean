import Thesis.MBonacciPrefixLimit
import Thesis.PalPrefixRatio

open Filter Topology

namespace Thesis.MBonacci

/-- The density of the word represented in the same rational-cut form as
`prop:insertion`. The enumeration and its recurrence are the cited
Fischler input in the proof of `prop:mbonacci`. -/
theorem below_density_of_prefix_recurrence (n : Nat) (w : Nat → α) (lengths : Nat → Nat)
    (hmono : StrictMono lengths)
    (henum : ∀ k, PalPrefix w k ↔ ∃ i, lengths i = k)
    (hFischler : PrefixLengthRecurrence n lengths)
    {p q : Nat} (hq : 0 < q) :
    BelowPalDensity w p q ↔ (p : ℝ) / q < 1 / beta n := by
  have hβ : beta n ≠ 0 := (zero_lt_one.trans (beta_spec n).1).ne'
  have hlim := (prefix_ratio_tendsto_beta n lengths hmono hFischler).inv₀ hβ
  simp only [inv_div] at hlim
  exact belowPalDensity_iff_of_ratio_limit hmono henum (by simpa only [one_div] using hlim) hq

end Thesis.MBonacci
