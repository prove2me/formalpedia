-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_EulerBricks
-- name    : Algebra_AbstractAlgebra_EulerBricks
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:01.336468+00:00
-- url     : https://prove2.me/theorems/58bd5856-f914-4595-9088-8295261734fc
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_EulerBricks
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.EulerBricks`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/EulerBricks.lean by skeleton subtraction
import Mathlib
/-
# Perfect Cuboid — Euler Brick Families

We construct infinite families of Euler bricks (face diagonals all integral)
and prove the existence of arbitrarily large Euler bricks.
-/

namespace PerfectCuboid

/-- A natural number is a perfect square. -/
def IsSquare (n : ℕ) : Prop := ∃ k : ℕ, k ^ 2 = n

/-- An Euler brick: all three face diagonals are integers. -/
def IsEulerBrick (x y z : ℕ) : Prop :=
  IsSquare (x ^ 2 + y ^ 2) ∧
  IsSquare (x ^ 2 + z ^ 2) ∧
  IsSquare (y ^ 2 + z ^ 2)


/-
Scaling preserves the Euler brick property.
-/

/-
There exist arbitrarily large Euler bricks.
This follows from scaling the (44, 117, 240) brick.
-/

/-
Scaling the (44,117,240) brick gives an infinite family.
-/



end PerfectCuboid


