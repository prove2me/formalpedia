-- Prove2me | Theorems.Thm_BookSixth_lipschitz_cutoff_infred_nonempty
-- name    : BookSixth.lipschitz_cutoff_infred_nonempty
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T21:04:41.652988+00:00
-- url     : https://prove2.me/theorems/77bed85d-fdcd-46f1-b4cc-1bdfd4bbc4b5
-- title:
--   A nonempty set admits a Lipschitz cut-off that is one on its thickening, zero off twice that thickening, and bounded between zero and one
-- statement:
--   Every nonempty subset K of three-dimensional real space with its supremum norm admits a Lipschitz cut-off function chi taking values in the unit interval, equal to one on the closed d-thickening of K, equal to zero off the closed 2d-thickening of K, and satisfying a Lipschitz bound with the single constant 1/d.
--
--   The Lipschitz constant is finite but is NOT required to be less than one, and that is the whole point. In the cut-off patching construction that builds the ambient isotopy for the round-circle motion theorem, the cut-off is equal to one on a neighbourhood of a component, so no useful bound can force its Lipschitz constant below one. What matters instead is that the constant 1/d is finite and is a function only of the fixed geometric clearance d, not of the size of the motion. Since the displacement estimate scales as (1/d) times the size of the motion, the patched map still satisfies a displacement-Lipschitz hypothesis below one once the motion is subdivided finely enough.
--
--   The witness is the distance-based cut-off
--       chi x = max 0 (min 1 ((2d - dist(x, K)) / d)),
--   where dist(x, K) is the infimum distance from x to K. That the distance to a set is 1-Lipschitz, and that taking a minimum or maximum with a constant preserves a Lipschitz bound, are the two analytic facts used; both are standard in Mathlib.
--
--   The hypothesis is that K is nonempty rather than that K is compact. Compactness alone does not imply nonemptiness, and the construction genuinely needs a point of K to compare distances against, because the thickening of the empty set is empty while the cut-off is still required to be a function on all of space.
-- source:
--   Chapter 15 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The analytic input is Metric.lipschitz_infDist_pt (Mathlib/Topology/MetricSpace/HausdorffDistance.lean:664), which makes the distance to a fixed set 1-Lipschitz, together with LipschitzWith.max_const and LipschitzWith.min_const (Mathlib/Topology/MetricSpace/Lipschitz.lean:190 and :196), which preserve the constant. The thickening notions are Metric.thickening and Metric.cthickening (Mathlib/Topology/MetricSpace/Thickening.lean:51 and :191), and the membership criterion is Metric.mem_cthickening_iff (Thickening.lean:195). In the mission this is instantiated with a round circle, whose nonemptiness is immediate from its range parametrisation and whose compactness is BookSixth.round_circle_is_compact (447ecc36), Proved. This is the last missing ingredient of the analytic layer of the isotopy extension; it feeds BookSixth.bump_perturbation_is_homeomorph_v3 (2691f203), Proved.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.lipschitz_cutoff_infred_nonempty {K : Set Space3} (hK : K.Nonempty) {d : ℝ} (hd : 0 < d) :
    ∃ chi : Space3 → ℝ,
      (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) ∧
      (∀ x, x ∈ Metric.cthickening d K → chi x = 1) ∧
      (∀ x, x ∉ Metric.cthickening (2 * d) K → chi x = 0) ∧
      LipschitzWith (Real.toNNReal (1 / d)) chi := by sorry
