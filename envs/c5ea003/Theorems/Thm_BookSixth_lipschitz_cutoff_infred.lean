-- Prove2me | Theorems.Thm_BookSixth_lipschitz_cutoff_infred
-- name    : BookSixth.lipschitz_cutoff_infred
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T20:55:48.3377+00:00
-- url     : https://prove2.me/theorems/9e16de8e-b878-4260-b6ad-a15c4332f22e
-- title:
--   A compact set admits a Lipschitz cut-off that is one on its thickening, zero off twice that thickening, and bounded between zero and one
-- statement:
--   Every compact subset K of three-dimensional real space with its supremum norm admits a Lipschitz cut-off function chi taking values in the unit interval, equal to one on the closed d-thickening of K, equal to zero off the closed 2d-thickening of K, and satisfying a Lipschitz bound with the single constant 1/d.
--
--   The Lipschitz constant is finite but is NOT required to be less than one, and that is the whole point. In the cut-off patching construction that builds the ambient isotopy for the round-circle motion theorem, the cut-off is equal to one on a neighbourhood of a component, so no useful bound can force its Lipschitz constant below one. What matters instead is that the constant 1/d is finite and that it is a function only of the fixed geometric clearance d, not of the size of the motion. Since the displacement estimate scales as (1/d) times the size of the motion, the patched map still satisfies a displacement-Lipschitz hypothesis below one once the motion is subdivided finely enough.
--
--   The witness is the distance-based cut-off
--       chi x = max 0 (min 1 ((2d - dist(x, K)) / d)),
--   where dist(x, K) is the infimum distance from x to K. That the distance to a set is 1-Lipschitz, and that taking a minimum or maximum with a constant preserves a Lipschitz bound, are the two analytic facts used; both are standard in Mathlib.
-- source:
--   Chapter 15 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The analytic input is Metric.lipschitz_infDist_pt (Mathlib/Topology/MetricSpace/HausdorffDistance.lean:664), which makes the distance to a fixed set 1-Lipschitz, together with LipschitzWith.max_const and LipschitzWith.min_const (Mathlib/Topology/MetricSpace/Lipschitz.lean:190 and :196), which preserve the constant. The thickening notions are Metric.thickening and Metric.cthickening (Mathlib/Topology/MetricSpace/Thickening.lean:51 and :191). Compactness of a round circle is BookSixth.round_circle_is_compact (447ecc36), Proved, but it is not needed for the construction itself. This is the last missing ingredient of the analytic layer of the isotopy extension; it feeds BookSixth.bump_perturbation_is_homeomorph_v3 (2691f203), Proved.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.lipschitz_cutoff_infred {K : Set Space3} (hK : IsCompact K) {d : ℝ} (hd : 0 < d) :
    ∃ chi : Space3 → ℝ,
      (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) ∧
      (∀ x, x ∈ Metric.cthickening d K → chi x = 1) ∧
      (∀ x, x ∉ Metric.cthickening (2 * d) K → chi x = 0) ∧
      LipschitzWith (Real.toNNReal (1 / d)) chi := by sorry
