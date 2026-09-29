-- Prove2me | Theorems.Thm_SplitGeometryCurvature_sechSq_eq_one_iff
-- name    : SplitGeometryCurvature.sechSq_eq_one_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:36:52.4889+00:00
-- url     : https://prove2.me/theorems/ed04d44f-ca6e-40b6-be66-116af378eda5
-- title:
--   Squared hyperbolic secant equals one exactly at zero.
-- statement:
--   Squared hyperbolic secant equals one exactly at zero.
--
--   ```lean
--   theorem SplitGeometryCurvature.sechSq_eq_one_iff(x : ℝ) : sechSq x = 1 ↔ x = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SplitGeometryCurvature.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SplitGeometryCurvature.lean#L107

-- Thm stub generated from Novelty/SplitGeometryCurvature.lean
import Mathlib
import Definitions.Def_Novelty_SplitGeometryCurvature

/-!
# The actual curvature phase portrait of split geometry

For the metric

`ds² = dx² / cosh² y + cosh² x · dy²`,

`SplitGeometry.KGauss_eq` computes the Gaussian curvature as

`-cosh² y - sech² x + 2 sech² x sech² y`.

The main result here is that this curvature is never positive.  It vanishes only
at the origin and is strictly negative everywhere else.  Thus the proposed
sign-changing field `sech² x - sech² y` is not the Gaussian curvature phase
portrait of this metric: the actual metric has no positive-curvature region and
its two diagonal lines are not flat (apart from their common origin).
-/

open SplitGeometryCurvature

open Real

theorem SplitGeometryCurvature.sechSq_eq_one_iff(x : ℝ) : sechSq x = 1 ↔ x = 0 := by sorry
