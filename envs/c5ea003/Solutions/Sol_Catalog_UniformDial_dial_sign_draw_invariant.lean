-- Prove2me | solution 1 for Catalog.UniformDial.dial_sign_draw_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:19:23.897635+00:00
-- url     : https://prove2.me/submissions/138fc5d8-d2cf-49b7-ba9a-9a80f641ccd8

-- Sol generated from Combinatorics/UniformDialDrawInvariance.lean
import Mathlib
import Definitions.Def_Combinatorics_UniformDialDrawInvariance
import Theorems.Thm_Catalog_UniformDial_wcov_eq_half_double_sum
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










/-- **No dilution, strict form.**  If the population is comonotone and the regime charges
two keys that are strictly concordant, the dial's covariance is strictly positive.  In
particular a full-support unbalanced regime signals exactly when a balanced one does. -/
theorem wcov_pos_of_comonotone {x y : ι → ℝ} (R : DrawRegime ι) (h : Comonotone x y)
    {a b : ι} (ha : 0 < R.p a) (hb : 0 < R.p b) (hab : 0 < (x a - x b) * (y a - y b)) :
    0 < wcov R.p x y := by
  have h2 := wcov_eq_half_double_sum (x := x) (y := y) R.total
  have hpos : 0 < ∑ i, ∑ j, R.p i * R.p j * ((x i - x j) * (y i - y j)) := by
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (R.nonneg i) (R.nonneg j)) (h i j)) ⟨a, Finset.mem_univ a, ?_⟩
    refine Finset.sum_pos' (fun j _ =>
      mul_nonneg (mul_nonneg (R.nonneg a) (R.nonneg j)) (h a j)) ⟨b, Finset.mem_univ b, ?_⟩
    exact mul_pos (mul_pos ha hb) hab
  linarith





variable {p q x y : ι → ℝ} {Mx My : ℝ}






open Catalog.UniformDial in
theorem solution{x y : ι → ℝ} (R S : DrawRegime ι)
    (hR : ∀ i, 0 < R.p i) (hS : ∀ i, 0 < S.p i) (h : Comonotone x y)
    {a b : ι} (hab : 0 < (x a - x b) * (y a - y b)) :
    0 < wcov R.p x y ∧ 0 < wcov S.p x y :=
  ⟨wcov_pos_of_comonotone R h (hR a) (hR b) hab,
   wcov_pos_of_comonotone S h (hS a) (hS b) hab⟩
