-- Prove2me | Theorems.Thm_PerfectCuboidResearch_scale_euler_brick
-- name    : PerfectCuboidResearch.scale_euler_brick
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:35:41.326619+00:00
-- url     : https://prove2.me/theorems/7213ecf9-13c0-444a-8d80-6cccc211e466
-- title:
--   Scaling preserves all integral face diagonals.
-- statement:
--   Scaling preserves all integral face diagonals.  Positivity of the scale is
--   not needed: the zero scale is algebraically valid as well.
--
--   ```lean
--   theorem PerfectCuboidResearch.scale_euler_brick{x y z : ℕ} (k : ℕ)
--       (h : IsEulerBrick x y z) : IsEulerBrick (k * x) (k * y) (k * z) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PerfectCuboid/AlgebraicSurface.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PerfectCuboid/AlgebraicSurface.lean#L50

-- Thm stub generated from Geometry/PerfectCuboid/AlgebraicSurface.lean
import Mathlib
import Definitions.Def_Geometry_PerfectCuboid_AlgebraicSurface
/-
# Perfect cuboids: an Euler brick near-miss and its algebraic surface

This file gives a self-contained formalization of Euler bricks and perfect
cuboids.  It verifies the classical brick `(44,117,240)`, proves that its space
diagonal is not integral, derives the diagonal-cone equation, and gives a
rational parametrization of the quadric underlying the normalized equations.
-/

open PerfectCuboidResearch

theorem PerfectCuboidResearch.scale_euler_brick{x y z : ℕ} (k : ℕ)
    (h : IsEulerBrick x y z) : IsEulerBrick (k * x) (k * y) (k * z) := by sorry
