-- Prove2me | Theorems.Thm_SplitGeometryCurvature_curvature_parameter_nonpos
-- name    : SplitGeometryCurvature.curvature_parameter_nonpos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:36:55.716753+00:00
-- url     : https://prove2.me/theorems/02a17456-53e6-48d2-b21e-9a862c0bc98c
-- title:
--   The elementary inequality controlling the curvature expression.
-- statement:
--   The elementary inequality controlling the curvature expression.  It is
--   stated on the exact range `(0,1]` of squared hyperbolic secants.
--
--   ```lean
--   theorem SplitGeometryCurvature.curvature_parameter_nonpos{a b : ℝ}
--       (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
--       -(1 / b) - a + 2 * a * b ≤ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SplitGeometryCurvature.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SplitGeometryCurvature.lean#L47

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

theorem SplitGeometryCurvature.curvature_parameter_nonpos{a b : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    -(1 / b) - a + 2 * a * b ≤ 0 := by sorry
