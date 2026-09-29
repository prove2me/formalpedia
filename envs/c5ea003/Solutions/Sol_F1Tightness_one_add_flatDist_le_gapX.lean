-- Prove2me | solution 1 for F1Tightness.one_add_flatDist_le_gapX
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:07:53.256949+00:00
-- url     : https://prove2.me/submissions/959a6789-33f3-49dc-89eb-0af0fd8350cc

-- Sol generated from Probability/F1TightnessQuantitative.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessQuantitative
import Theorems.Thm_F1Tightness_flatDist_nonneg
import Theorems.Thm_F1Tightness_scanCost_le_baseCost_sub_flatDist
import Theorems.Thm_F1Tightness_scanCost_le_card
import Theorems.Thm_F1Tightness_scanCost_pos

/-!
# A quantitative (L¹) strengthening of the F1 master inequality

`Probability.F1TightnessCore` proves that on an antitone non-flat profile the
slack factor `X = C₀/c_asc` is strictly larger than one, so the master bound is
never attained; but `one_lt_gapX` is qualitative — it gives no number.

This file supplies the number.  Write

`flatDist p = ∑ i, |p i − 1/M|`

for the L¹ distance of the profile to the flat profile.  Then, for every
antitone profile,

* `scanCost_le_baseCost_sub_flatDist` — `c_asc ≤ C₀ − ‖p − flat‖₁ / 2`;
* `one_add_flatDist_le_gapX` — `1 + ‖p − flat‖₁/(2M) ≤ X`;
* `speedup_mul_le_bound_quantitative` — **the refined master inequality**
  `S · (1 + ‖p − flat‖₁/(2M)) ≤ bound`, i.e. `S ≤ bound/(1 + V)` with the
  explicit, computable dispersion functional `V = ‖p − flat‖₁/(2M)`;
* `flatDist_eq_zero_iff` — `V` vanishes exactly on the flat profile, the case
  the three independent tests reject pool-side.

The proof route is the pairwise expansion `sum_pairs_identity` of the core file,
kept with its quadratic remainder instead of discarded: for an antitone profile
each pairwise term of the Chebyshev double sum is bounded below by `|p i − p j|`
in absolute value, and the triangle inequality converts the resulting double sum
into the L¹ distance to flat.  This is the shape asked for by direction 3 of
`FUTURE_DIRECTIONS.md`, with the absolute constant `c = 1` in the normalisation
`V = ‖p − flat‖₁/(2M)`.
-/

open F1Tightness

open Finset

variable {M : ℕ}











/-! ## Non-vacuity: an explicit profile with a positive dispersion -/








open F1Tightness in
theorem solution{p : Fin M → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i : Fin M, p i = 1) (hanti : Antitone p) :
    1 + flatDist p / (2 * (M : ℝ)) ≤ gapX p := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hc := scanCost_pos hp hsum
  have hcM := scanCost_le_card hp hsum
  have hb := scanCost_le_baseCost_sub_flatDist hsum hanti
  have hL := flatDist_nonneg p
  unfold gapX
  rw [le_div_iff₀ hc]
  have hstep : flatDist p / (2 * (M : ℝ)) * scanCost p ≤ flatDist p / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith
