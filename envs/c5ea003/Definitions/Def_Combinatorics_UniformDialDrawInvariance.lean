-- Prove2me | Definitions.Def_Combinatorics_UniformDialDrawInvariance
-- name    : Combinatorics_UniformDialDrawInvariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:56:19.695117+00:00
-- url     : https://prove2.me/theorems/3c10ce49-2cda-4dba-a1c5-c2259730ad72
-- title:
--   Aether Catalog definitions — Combinatorics_UniformDialDrawInvariance
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.UniformDialDrawInvariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/UniformDialDrawInvariance.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.UniformDial

variable {ι : Type*} [Fintype ι]

/-- Weighted (draw-regime) mean of `x`. -/
noncomputable def wmean (p x : ι → ℝ) : ℝ := ∑ i, p i * x i

/-- Weighted (draw-regime) covariance of `x` and `y`. -/
noncomputable def wcov (p x y : ι → ℝ) : ℝ :=
  ∑ i, p i * (x i - wmean p x) * (y i - wmean p y)

/-- Weighted (draw-regime) variance. -/
noncomputable def wvar (p x : ι → ℝ) : ℝ := wcov p x x

/-- A draw regime: a probability weighting of the population. -/
structure DrawRegime (ι : Type*) [Fintype ι] where
  /-- the probability mass of each key -/
  p : ι → ℝ
  nonneg : ∀ i, 0 ≤ p i
  total : ∑ i, p i = 1




/-- The population is *comonotone*: no pair of keys is discordant (a larger footprint is
never paired with a strictly smaller rate). -/
def Comonotone (x y : ι → ℝ) : Prop := ∀ i j, 0 ≤ (x i - x j) * (y i - y j)






section Stability

variable {p q x y : ι → ℝ} {Mx My : ℝ}




end Stability

end Catalog.UniformDial


