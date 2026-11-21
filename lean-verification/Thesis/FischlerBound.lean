import Thesis.PalindromicDensityReal
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Algebra.Ring.Periodic

open Set Filter Topology Real
open scoped goldenRatio

namespace Thesis

/-- A period of the finite prefix ending just before index `n`. -/
private def PrefixPeriod (w : ℕ → α) (n d : ℕ) : Prop :=
  ∀ i, i + d < n → w (i + d) = w i

/-- Reflection in two palindromic prefixes gives the period equal to their gap. -/
private theorem prefixPeriod_of_pal {w : ℕ → α} {n d : ℕ}
    (hn : PalPrefix w n) (hnd : PalPrefix w (n + d)) :
    PrefixPeriod w (n + d) d := by
  intro i hi
  have h := hnd (i + d) hi
  rw [show n + d - 1 - (i + d) = n - 1 - i by omega] at h
  exact h.trans (hn i (by omega)).symm

/-- A period of a palindrome cuts off a palindromic border. -/
private theorem pal_of_prefixPeriod {w : ℕ → α} {n d : ℕ}
    (hn : PalPrefix w (n + d)) (hp : PrefixPeriod w (n + d) d) : PalPrefix w n := by
  intro i hi
  have he := hn (i + d) (by omega)
  rw [show n + d - 1 - (i + d) = n - 1 - i by omega] at he
  exact (hp i (by omega)).symm.trans he

/-- For consecutive palindromic lengths the gap is the least positive period
of the longer prefix. A shorter positive period would give an intermediate border. -/
private theorem gap_le_period {w : ℕ → α} {n d p : ℕ}
    (h : ConsecutivePalPrefixes w n (n + d)) (hp : 0 < p)
    (hper : PrefixPeriod w (n + d) p) : d ≤ p := by
  by_contra! hlt
  let m := n + d - p
  have hm : m + p = n + d := by dsimp [m]; omega
  have hpal := h.2.2.2.1
  rw [← hm] at hper hpal
  exact h.2.2.2.2 m (by dsimp [m]; omega) (by dsimp [m]; omega)
    (pal_of_prefixPeriod hpal hper)

/-- If the next prefix has length at most the sum of the previous two, the
prefix and its reflected copy overlap by at least the preceding gap. Both
copies then carry that period across the entire new prefix. -/
theorem palPrefix_gaps_eq_of_overlap {w : ℕ → α} {a b c : ℕ}
    (hab : ConsecutivePalPrefixes w a b) (hbc : ConsecutivePalPrefixes w b c)
    (hsize : c ≤ a + b) : c - b = b - a := by
  let d := b - a
  let e := c - b
  have ha := hab.2.1
  have hb := hbc.2.1
  have h₁ : a + d = b := by dsimp [d]; omega
  have h₂ : b + e = c := by dsimp [e]; omega
  have hd := prefixPeriod_of_pal hab.2.2.1 (h₁.symm ▸ hab.2.2.2.1)
  have he := prefixPeriod_of_pal hbc.2.2.1 (h₂.symm ▸ hbc.2.2.2.1)
  rw [h₁] at hd
  rw [h₂] at he
  have hd' : PrefixPeriod w c d := by
    intro i hi
    by_cases h : i + d < b
    · exact hd i h
    · have hie : e ≤ i := by dsimp [d, e] at *; omega
      let j := i - e
      have hj : j + e = i := by dsimp [j]; omega
      calc
        w (i + d) = w (j + d) := by
          simpa only [show j + d + e = i + d by omega] using
            he (j + d) (by omega)
        _ = w j := hd j (by omega)
        _ = w i := by simpa only [hj] using (he j (by omega)).symm
  have he' : PrefixPeriod w b e := fun i hi => he i (by omega)
  have lo := gap_le_period (h₁.symm ▸ hab) (p := e) (by dsimp [e]; omega) (h₁.symm ▸ he')
  have hi := gap_le_period (h₂.symm ▸ hbc) (p := d) (by dsimp [d]; omega) (h₂.symm ▸ hd')
  exact le_antisymm hi lo

/-- The general upper bound cited as Fischler's theorem in §3.6. A density
above the reciprocal golden ratio forces the sum-overlap inequality at
every sufficiently late triple. The common gap is then a period of the word. -/
theorem periodic_of_inv_golden_lt_palindromicDensity {w : ℕ → α}
    (h : 1 / φ < palindromicDensity w) : ∃ d : ℕ, 0 < d ∧ Function.Periodic w d := by
  classical
  have hinf : {n | PalPrefix w n}.Infinite := by
    intro hf
    rw [palindromicDensity_of_finite hf] at h
    exact (not_lt_of_ge (by positivity)) h
  let L := Nat.nth (PalPrefix w)
  have hL : StrictMono L := Nat.nth_strictMono hinf
  have henum (n : ℕ) : PalPrefix w n ↔ ∃ i, L i = n := by
    change n ∈ {m | PalPrefix w m} ↔ _
    rw [← Nat.range_nth_of_infinite hinf]
    rfl
  have hratio := palindromicDensity_eq_reciprocal_limsup hL henum
  have hlim : 1 / φ < liminf (fun i => (L i : ℝ) / L (i+1)) atTop := by
    rwa [hratio, reciprocal_limsup_eq_liminf hL] at h
  have hlate := eventually_lt_of_lt_liminf hlim
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall
      (show ∀ i, (0 : ℝ) ≤ (L i : ℝ) / L (i+1) from fun _ => by positivity)))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hlate
  let N := K + 1
  have hpos (i : ℕ) (hi : N ≤ i) : 0 < L i := (hL (show 0 < i by dsimp [N] at hi; omega)).trans_le' (Nat.zero_le _)
  have bound (i : ℕ) (hi : N ≤ i) : (L (i+1) : ℝ) < φ * L i := by
    have hp : (0 : ℝ) < L (i+1) := by exact_mod_cast hpos (i+1) (by omega)
    have hh := (div_lt_div_iff₀ gold_pos hp).1 (hK i (by dsimp [N] at hi; omega))
    linarith
  have hcon (i : ℕ) (hi : N ≤ i) := consecutive_of_enumeration hL henum i (hpos i hi)
  have eqgap (i : ℕ) (hi : N ≤ i) : L (i+2) - L (i+1) = L (i+1) - L i := by
    apply palPrefix_gaps_eq_of_overlap (hcon i hi) (hcon (i+1) (by omega))
    have h₁ := bound i hi
    have h₂ := bound (i+1) (by omega)
    have h₃ := mul_lt_mul_of_pos_left h₁ (sub_pos.2 one_lt_gold)
    have hid : (φ - 1) * (φ * (L i : ℝ)) = L i := by
      have hgold : (φ - 1) * φ = 1 := by nlinarith [gold_sq]
      rw [← mul_assoc, hgold, one_mul]
    rw [hid] at h₃
    exact_mod_cast (show (L (i+2) : ℝ) ≤ L i + L (i+1) by linarith)
  let d := L (N+1) - L N
  have hd (j : ℕ) : L (N+j+1) - L (N+j) = d := by
    induction j with
    | zero => rfl
    | succ j ih => exact (eqgap (N+j) (by omega)).trans ih
  refine ⟨d, Nat.sub_pos_of_lt (hL (Nat.lt_succ_self N)), ?_⟩
  intro i
  let j := i + d + 1
  have hstep := hd j
  have hlt : L (N+j) < L (N+j+1) := hL (Nat.lt_succ_self (N+j))
  have hlen : L (N+j) + d = L (N+j+1) := by omega
  have hpal (n : ℕ) := (henum _).2 ⟨n, rfl⟩
  have hp := prefixPeriod_of_pal (hpal (N+j)) (hlen.symm ▸ hpal (N+j+1))
  have hlarge : N+j ≤ L (N+j) := hL.id_le _
  exact hp i (by dsimp [j] at *; omega)

theorem palindromicDensity_le_inv_golden {w : ℕ → α}
    (haper : ¬ ∃ d : ℕ, 0 < d ∧ Function.Periodic w d) :
    palindromicDensity w ≤ 1 / φ :=
  le_of_not_gt fun h => haper (periodic_of_inv_golden_lt_palindromicDensity h)

end Thesis
