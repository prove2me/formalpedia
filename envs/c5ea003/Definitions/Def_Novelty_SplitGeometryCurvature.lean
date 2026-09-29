-- Prove2me | Definitions.Def_Novelty_SplitGeometryCurvature
-- name    : Novelty_SplitGeometryCurvature
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:50.226743+00:00
-- url     : https://prove2.me/theorems/9acce83e-d5f2-4ef6-a347-0eb2619365d6
-- title:
--   Aether Catalog definitions — Novelty_SplitGeometryCurvature
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SplitGeometryCurvature`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SplitGeometryCurvature.lean by skeleton subtraction
import Mathlib

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

namespace SplitGeometryCurvature

open Real

/-- Squared hyperbolic secant. -/
noncomputable def sechSq (t : ℝ) : ℝ := 1 / Real.cosh t ^ 2

/-- The Gaussian curvature obtained from the orthogonal-metric curvature formula
for `ds² = dx²/cosh² y + cosh² x · dy²`. -/
noncomputable def gaussianCurvature (x y : ℝ) : ℝ :=
  -(Real.cosh y) ^ 2 - sechSq x + 2 * sechSq x * sechSq y











/-- The proposed phase field, included to compare its zero locus with the true
curvature. -/
noncomputable def phaseField (x y : ℝ) : ℝ := sechSq x - sechSq y



end SplitGeometryCurvature


