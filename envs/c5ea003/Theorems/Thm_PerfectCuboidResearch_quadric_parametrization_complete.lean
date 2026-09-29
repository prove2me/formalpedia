-- Prove2me | Theorems.Thm_PerfectCuboidResearch_quadric_parametrization_complete
-- name    : PerfectCuboidResearch.quadric_parametrization_complete
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:35:42.567335+00:00
-- url     : https://prove2.me/theorems/09335899-5c7e-4717-854d-ab48f17c80c3
-- title:
--   The parametrization is complete away from its base point: every rational
-- statement:
--   The parametrization is complete away from its base point: every rational
--   point on the quadric with `u ≠ 1` is recovered by taking the slopes
--   `p = v/(u-1)` and `q = w/(u-1)`.
--
--   ```lean
--   theorem PerfectCuboidResearch.quadric_parametrization_complete    {u v w : ℚ} (hquad : OnCuboidQuadric u v w) (hu : u ≠ 1) :
--       let p := v / (u - 1)
--       let q := w / (u - 1)
--       1 + p ^ 2 - q ^ 2 ≠ 0 ∧
--         u = (p ^ 2 - q ^ 2 - 1) / (1 + p ^ 2 - q ^ 2) ∧
--         v = (-2 * p) / (1 + p ^ 2 - q ^ 2) ∧
--         w = (-2 * q) / (1 + p ^ 2 - q ^ 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PerfectCuboid/AlgebraicSurface.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PerfectCuboid/AlgebraicSurface.lean#L128

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

theorem PerfectCuboidResearch.quadric_parametrization_complete    {u v w : ℚ} (hquad : OnCuboidQuadric u v w) (hu : u ≠ 1) :
    let p := v / (u - 1)
    let q := w / (u - 1)
    1 + p ^ 2 - q ^ 2 ≠ 0 ∧
      u = (p ^ 2 - q ^ 2 - 1) / (1 + p ^ 2 - q ^ 2) ∧
      v = (-2 * p) / (1 + p ^ 2 - q ^ 2) ∧
      w = (-2 * q) / (1 + p ^ 2 - q ^ 2) := by sorry
