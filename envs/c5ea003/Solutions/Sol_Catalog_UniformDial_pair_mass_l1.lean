-- Prove2me | solution 1 for Catalog.UniformDial.pair_mass_l1
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:42:20.125508+00:00
-- url     : https://prove2.me/submissions/a88c54da-4c7c-466f-871a-07ee005e0cd9

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
theorem solution(hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    ∑ i, ∑ j, |p i * p j - q i * q j| ≤ 2 * ∑ i, |p i - q i| := by
  set S := ∑ i, |p i - q i| with hS
  have step : ∀ i, ∑ j, |p i * p j - q i * q j| ≤ p i * S + |p i - q i| := by
    intro i
    have bound : ∀ j, |p i * p j - q i * q j| ≤ p i * |p j - q j| + |p i - q i| * q j := by
      intro j
      have : p i * p j - q i * q j = p i * (p j - q j) + (p i - q i) * q j := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hp0 i), abs_of_nonneg (hq0 j)]
    calc ∑ j, |p i * p j - q i * q j|
        ≤ ∑ j, (p i * |p j - q j| + |p i - q i| * q j) :=
          Finset.sum_le_sum fun j _ => bound j
      _ = p i * S + |p i - q i| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq, hS, mul_one]
  calc ∑ i, ∑ j, |p i * p j - q i * q j|
      ≤ ∑ i, (p i * S + |p i - q i|) := Finset.sum_le_sum fun i _ => step i
    _ = S + S := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul, ← hS]
    _ = 2 * S := by ring
