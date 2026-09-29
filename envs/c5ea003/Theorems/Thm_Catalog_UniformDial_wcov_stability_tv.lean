-- Prove2me | Theorems.Thm_Catalog_UniformDial_wcov_stability_tv
-- name    : Catalog.UniformDial.wcov_stability_tv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:03:31.338676+00:00
-- url     : https://prove2.me/theorems/e8d48be1-e74d-472e-95de-b574fb756d0b
-- title:
--   Quantitative draw-regime invariance.
-- statement:
--   **Quantitative draw-regime invariance.**  If the footprint values span at most `Mx`
--   and the rates span at most `My`, then the dial's covariance under two draw regimes differs
--   by at most `Mx * My` times their ℓ¹ distance (= twice their total-variation distance).
--   Two regimes that are close in ℓ¹ therefore *must* report the dial "identical within
--   noise"; there is no room for a dilution effect.
--
--   ```lean
--   theorem Catalog.UniformDial.wcov_stability_tv(hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
--       (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
--       (hx : ∀ i j, |x i - x j| ≤ Mx) (hy : ∀ i j, |y i - y j| ≤ My) :
--       |wcov p x y - wcov q x y| ≤ Mx * My * ∑ i, |p i - q i| := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/UniformDialDrawInvariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/UniformDialDrawInvariance.lean#L193

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















variable {p q x y : ι → ℝ} {Mx My : ℝ}

theorem Catalog.UniformDial.wcov_stability_tv(hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (hx : ∀ i j, |x i - x j| ≤ Mx) (hy : ∀ i j, |y i - y j| ≤ My) :
    |wcov p x y - wcov q x y| ≤ Mx * My * ∑ i, |p i - q i| := by sorry
