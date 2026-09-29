-- Prove2me | solution 1 for Catalog.UniformDial.wcov_eq_half_double_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:17:44.037407+00:00
-- url     : https://prove2.me/submissions/5f39df61-a5f7-4107-ac53-3df9aaba4d4e

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






/-- Raw-moment form of the weighted covariance. -/
lemma wcov_eq_raw {p x y : ι → ℝ} (hp : ∑ i, p i = 1) :
    wcov p x y = (∑ i, p i * x i * y i) - (∑ i, p i * x i) * (∑ i, p i * y i) := by
  simp only [wcov, wmean]
  have key : ∀ i, p i * (x i - ∑ j, p j * x j) * (y i - ∑ j, p j * y j)
      = p i * x i * y i - (∑ j, p j * y j) * (p i * x i) - (∑ j, p j * x j) * (p i * y i)
        + (∑ j, p j * x j) * (∑ j, p j * y j) * p i := by
    intro i; ring
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
  ring









variable {p q x y : ι → ℝ} {Mx My : ℝ}






open Catalog.UniformDial in
theorem solution{p x y : ι → ℝ} (hp : ∑ i, p i = 1) :
    (2 : ℝ) * wcov p x y = ∑ i, ∑ j, p i * p j * ((x i - x j) * (y i - y j)) := by
  have expand : ∑ i, ∑ j, p i * p j * ((x i - x j) * (y i - y j))
      = ((∑ i, ∑ j, (p i * (x i * y i)) * p j) - (∑ i, ∑ j, (p i * x i) * (p j * y j))
        - (∑ i, ∑ j, (p i * y i) * (p j * x j))) + (∑ i, ∑ j, p i * (p j * (x j * y j))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [expand]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hp, mul_one]
  rw [wcov_eq_raw hp]
  have h1 : (∑ i, p i * (x i * y i)) = ∑ i, p i * x i * y i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h1]; ring
