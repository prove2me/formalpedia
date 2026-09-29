-- Prove2me | solution 1 for KTaxonomy.pin_overcharge_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:51:55.518076+00:00
-- url     : https://prove2.me/submissions/f2c09c82-e35d-4bcb-9620-37b4d3daa502

-- Sol generated from Cryptography/KTaxonomyRigidity.lean
import Mathlib
import Definitions.Def_Cryptography_KTaxonomyCensusEcon
import Theorems.Thm_KTaxonomy_census_argmin_iff
import Theorems.Thm_KTaxonomy_census_incr
import Theorems.Thm_KTaxonomy_census_two_step
import Theorems.Thm_KTaxonomy_one_le_kPin
import Theorems.Thm_KTaxonomy_pin_gap_general
import Theorems.Thm_KTaxonomy_pin_gap_one_iff_two_pow

/-!
# Rigidity of the k-taxonomy: price rescaling, tie sets, and the exact pin gap

Round three of the taxonomy.  The previous two files fixed the three budgets and proved the
exact identities relating them at unit query price and the argmin brackets at general width.
Here we close the three questions those results left open.

* **Price is a pure anchor rescaling** (`econ_eq_census_price`,
  `econ_argmin_iff_census_argmin_price`): for every price `c_q > 0`,
  `econ T₀ c_q k = c_q ⬝ (census (2 (T₀ - 1) / c_q) k + 1/2)`, so the economics optimum at
  price `c_q` is *exactly* the census optimum at the rescaled anchor `2 (T₀ - 1) / c_q`.
  The two-parameter taxonomy therefore collapses to the one-parameter census family.
* **Tie dichotomy** (`census_tie_iff`, `census_argmin_unique_of_not_two_pow`): the census
  argmin is a two-element set exactly at the dyadic widths `W = 2 ^ (k + 2)`, and is a
  singleton at every non-dyadic width.  So "the" census optimum is well defined off the
  dyadic locus, and ambiguous exactly on it.
* **Exact pin gap** (`pin_gap_one_iff_two_pow`): for an integer width `W ≥ 2` and a census
  optimum `k`, the gap `kPin W - k` equals `1` **iff** `W = 2 ^ (k + 1)`, and equals `2`
  otherwise.  Combined with `pin_gap_general` this determines the gap completely.

-- !-- Lab Notes -- !--
Hypothesizer (round 3):
 (H9)  Price enters only through the anchor: argmin of `econ T₀ c_q` = argmin of
       `census (2 (T₀ - 1) / c_q)`.                                              [BOLD]
 (H10) Ties happen exactly at dyadic widths.
 (H11) The pin gap is `2` at *non*-dyadic widths and `1` only when the width is exactly
       `2 ^ (k + 1)`.

Analyst: H11 is the informative correction of this round.  The natural guess from the
dyadic table (`argmin = {m-2, m-1}`, pin `m`, gaps `{2, 1}`) is that gap `1` is generic and
gap `2` is the dyadic exception.  The truth is the opposite: at `W = 3` the unique optimum
is `k = 0` while the pin is `2`, so the gap is `2`; a gap of `1` requires the width to sit
exactly on the power of two `2 ^ (k + 1)`.  This is a "needs a different statement" outcome
rather than a failure: the corrected statement is proved below, and it says the pin
overstates the work-optimal budget by *two* queries at almost every width.
-/

open KTaxonomy

/-! ## Price is a pure anchor rescaling -/



/-! ## The tie dichotomy -/




/-! ## The exact pin gap -/



/-! ## How much the pin overcharges -/




open KTaxonomy in
theorem solution(W k : ℕ) (hW : 2 ≤ W)
    (hk : ∀ j, census (W : ℝ) k ≤ census (W : ℝ) j) :
    1 / 2 ≤ census (W : ℝ) (kPin W) - census (W : ℝ) k ∧
      census (W : ℝ) (kPin W) - census (W : ℝ) k < 5 / 4 := by
  have hWpos : (0:ℝ) < (W : ℝ) := by exact_mod_cast (show 0 < W by omega)
  have hbr := (census_argmin_iff (W : ℝ) hWpos k).1 hk
  have hk1 : 1 ≤ kPin W := one_le_kPin hW
  have hlow : (2:ℝ) ^ (k + 1) ≤ (W : ℝ) := by
    rcases hbr.2 with hz | h
    · subst hz
      have : (2:ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
      simpa using this
    · exact h
  rcases pin_gap_general W k hW hk with hgap | hgap
  · have hWval : W = 2 ^ (k + 1) := (pin_gap_one_iff_two_pow W k hW hk).1 hgap
    have hpin : kPin W = k + 1 := by omega
    have hWr : (W : ℝ) = 2 ^ (k + 1) := by exact_mod_cast congrArg (Nat.cast (R := ℝ)) hWval
    have hinc := census_incr (W : ℝ) k
    have hp : (0:ℝ) < 2 ^ (k + 1) := by positivity
    have hval : census (W : ℝ) (kPin W) - census (W : ℝ) k = 1 / 2 := by
      rw [hpin, hinc, hWr]
      have : (2:ℝ) ^ (k + 2) = 2 ^ (k + 1) * 2 := by ring
      rw [this]
      field_simp
      norm_num
    rw [hval]
    norm_num
  · have hpin : kPin W = k + 2 := by omega
    have hstep := census_two_step (W : ℝ) k
    have hp3 : (0:ℝ) < 2 ^ (k + 3) := by positivity
    have hupper : (W : ℝ) ≤ 2 ^ (k + 2) := hbr.1
    have hstrict : (2:ℝ) ^ (k + 1) < (W : ℝ) := by
      rcases lt_or_eq_of_le hlow with h | h
      · exact h
      · exfalso
        have hWnat : W = 2 ^ (k + 1) := by exact_mod_cast h.symm
        have := (pin_gap_one_iff_two_pow W k hW hk).2 hWnat
        omega
    have e2 : (2:ℝ) ^ (k + 3) = 2 ^ (k + 1) * 4 := by ring
    have e1 : (2:ℝ) ^ (k + 2) = 2 ^ (k + 1) * 2 := by ring
    rw [e1] at hupper
    have hb1 : 3 * (W:ℝ) / 2 ^ (k + 3) ≤ 3 / 2 := by
      rw [div_le_iff₀ hp3, e2]
      nlinarith
    have hb2 : 3 / 4 < 3 * (W:ℝ) / 2 ^ (k + 3) := by
      rw [lt_div_iff₀ hp3, e2]
      nlinarith
    rw [hpin, hstep]
    constructor <;> linarith
