-- Prove2me | Definitions.Def_Geometry_PerfectCuboid_AlgebraicSurface
-- name    : Geometry_PerfectCuboid_AlgebraicSurface
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:34.714211+00:00
-- url     : https://prove2.me/theorems/445801d6-4f0f-4f61-a2ee-09100136eee8
-- title:
--   Aether Catalog definitions — Geometry_PerfectCuboid_AlgebraicSurface
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PerfectCuboid.AlgebraicSurface`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PerfectCuboid/AlgebraicSurface.lean by skeleton subtraction
import Mathlib
/-
# Perfect cuboids: an Euler brick near-miss and its algebraic surface

This file gives a self-contained formalization of Euler bricks and perfect
cuboids.  It verifies the classical brick `(44,117,240)`, proves that its space
diagonal is not integral, derives the diagonal-cone equation, and gives a
rational parametrization of the quadric underlying the normalized equations.
-/

namespace PerfectCuboidResearch

/-- `n` is a square of a natural number. -/
def IsSquare (n : ℕ) : Prop := ∃ k : ℕ, k ^ 2 = n

/-- All three face diagonals of the box are integral. -/
def IsEulerBrick (x y z : ℕ) : Prop :=
  IsSquare (x ^ 2 + y ^ 2) ∧
  IsSquare (x ^ 2 + z ^ 2) ∧
  IsSquare (y ^ 2 + z ^ 2)

/-- An Euler brick whose space diagonal is also integral. -/
def IsPerfectCuboid (x y z : ℕ) : Prop :=
  IsEulerBrick x y z ∧ IsSquare (x ^ 2 + y ^ 2 + z ^ 2)








/-- The affine quadric that appears after normalizing one edge of a perfect
cuboid. -/
def OnCuboidQuadric (u v w : ℚ) : Prop := w ^ 2 = u ^ 2 + v ^ 2 - 1




end PerfectCuboidResearch


