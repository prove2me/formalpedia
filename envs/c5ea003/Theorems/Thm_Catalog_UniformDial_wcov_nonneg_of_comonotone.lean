-- Prove2me | Theorems.Thm_Catalog_UniformDial_wcov_nonneg_of_comonotone
-- name    : Catalog.UniformDial.wcov_nonneg_of_comonotone
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:03:44.34438+00:00
-- url     : https://prove2.me/theorems/6ea0e521-4849-4fc4-a4e2-d33193314e83
-- title:
--   No dilution, qualitative form.
-- statement:
--   **No dilution, qualitative form.**  For a comonotone population the dial has
--   nonnegative covariance with the rate in *every* draw regime, however unbalanced.
--
--   ```lean
--   theorem Catalog.UniformDial.wcov_nonneg_of_comonotone{x y : ι → ℝ} (R : DrawRegime ι) (h : Comonotone x y) :
--       0 ≤ wcov R.p x y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/UniformDialDrawInvariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/UniformDialDrawInvariance.lean#L96

-- Thm stub generated from Combinatorics/UniformDialDrawInvariance.lean
import Mathlib
import Definitions.Def_Combinatorics_UniformDialDrawInvariance
/-
# The yield dial is draw-regime invariant

Setting.  A finite population `ι` of "keys".  Each key `i` carries a *footprint* `x i`
(the weight used by the dial) and a *yield rate* `y i`.  A **draw regime** is a
probability weighting `p : ι → ℝ` (`p ≥ 0`, `∑ p = 1`): uniform draws, balanced draws
and genuinely unbalanced draws are all instances of the same object.

The experimental claim under test (`DIAL-IS-DRAW-INVARIANT`) is that the association
between the footprint dial and the yield rate does **not** get diluted when the draw
regime is changed.  This file isolates the exact structural reason, and quantifies the
residual regime dependence:

* `wcov_eq_half_double_sum` — the Hoeffding/Chebyshev pair identity: the weighted
  covariance is a *pairwise* functional of the population.
* `wcov_nonneg_of_comonotone` — if the population is comonotone (no discordant pair),
  the dial has nonnegative covariance with the rate **in every draw regime**.
* `wcov_pos_of_comonotone` — strict positivity survives as soon as one strictly ordered
  pair is charged by the regime; hence full-support regimes cannot dilute the signal.
* `dial_sign_draw_invariant` — the two-regime form of the claim (uniform vs unbalanced).
* `wcov_monotone_comp_nonneg` — the same holds after arbitrary monotone re-encodings of
  footprint and rate, i.e. for rank (Spearman-type) versions of the dial.
* `wcov_stability_tv` — a quantitative bound: changing the draw regime moves the dial's
  covariance by at most `(range x) * (range y)` times the ℓ¹ (twice total variation)
  distance between the regimes.  "Identical within noise" is therefore forced whenever
  the two regimes are ℓ¹-close, and cannot be worse than this bound in general.

All statements are for an arbitrary finite index type; nothing here is specific to a
sampling seed.
-/

open Finset

open Catalog.UniformDial

variable {ι : Type*} [Fintype ι]

theorem Catalog.UniformDial.wcov_nonneg_of_comonotone{x y : ι → ℝ} (R : DrawRegime ι) (h : Comonotone x y) :
    0 ≤ wcov R.p x y := by sorry
