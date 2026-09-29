-- Prove2me | solution 1 for Catalog.UniformDial.comonotone_comp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:17:43.50801+00:00
-- url     : https://prove2.me/submissions/32123e06-cd7a-4b66-b403-bd2220c32be4

-- Sol generated from Combinatorics/UniformDialDrawInvariance.lean
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






open Catalog.UniformDial in
omit [Fintype ι] in
theorem solution{x y : ι → ℝ} {g h : ℝ → ℝ} (hg : Monotone g) (hh : Monotone h)
    (hxy : Comonotone x y) : Comonotone (g ∘ x) (h ∘ y) := by
  intro i j
  rcases lt_trichotomy (x i) (x j) with hx | hx | hx
  · have hy : y i ≤ y j := by
      by_contra hc
      push_neg at hc
      nlinarith [hxy i j]
    have h1 := hg hx.le; have h2 := hh hy
    simp only [Function.comp_apply]
    nlinarith
  · simp only [Function.comp_apply, hx, sub_self, zero_mul, le_refl]
  · have hy : y j ≤ y i := by
      by_contra hc
      push_neg at hc
      nlinarith [hxy i j]
    have h1 := hg hx.le; have h2 := hh hy
    simp only [Function.comp_apply]
    nlinarith
