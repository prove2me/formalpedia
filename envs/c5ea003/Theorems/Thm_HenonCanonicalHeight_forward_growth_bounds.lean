-- Prove2me | Theorems.Thm_HenonCanonicalHeight_forward_growth_bounds
-- name    : HenonCanonicalHeight.forward_growth_bounds
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:05.200027+00:00
-- url     : https://prove2.me/theorems/747a8929-66ec-4afc-a2f4-fd42ab7b19e2
-- title:
--   In the forward region, one Hénon step has the standard archimedean
-- statement:
--   In the forward region, one Hénon step has the standard archimedean
--   `1/3` and `5/3` growth bounds.
--
--   ```lean
--   theorem HenonCanonicalHeight.forward_growth_bounds{D : ℕ} {b x y : ℝ}
--       (hP : InForwardRegion D b (x, y)) :
--       (1 / 3 : ℝ) * |y| ^ D < |x + y ^ D + b| ∧
--         |x + y ^ D + b| < (5 / 3 : ℝ) * |y| ^ D := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HenonCanonicalHeight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HenonCanonicalHeight.lean#L42

-- Thm stub generated from Bridges/HenonCanonicalHeight.lean
import Mathlib
import Definitions.Def_Bridges_HenonCanonicalHeight

/-!
# Escape regions and normalized heights for a Hénon map

This file formalizes algebraic and analytic ingredients used in the study of the map
`φ(x,y) = (y, x + y^D + b)`.  The escape region below is a slightly strengthened,
robust version of the usual archimedean escape region: the additional condition
`3 |y| < |y|^D` makes forward invariance transparent even in the presence of
cancellation.  No global arithmetic-height machinery is assumed.
-/

open HenonCanonicalHeight

theorem HenonCanonicalHeight.forward_growth_bounds{D : ℕ} {b x y : ℝ}
    (hP : InForwardRegion D b (x, y)) :
    (1 / 3 : ℝ) * |y| ^ D < |x + y ^ D + b| ∧
      |x + y ^ D + b| < (5 / 3 : ℝ) * |y| ^ D := by sorry
