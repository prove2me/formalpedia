-- Prove2me | Definitions.Def_MovingSofa_ForMathlib_EuclideanSpace
-- name    : MovingSofa_ForMathlib_EuclideanSpace
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:59:33.158824+00:00
-- url     : https://prove2.me/theorems/641ccf6a-0077-4d88-950c-40da307f66d4
-- title:
--   Swapped plane coordinates
-- statement:
--   The map $p\mapsto(p_1,p_0)$ reading plane coordinates in reversed order, used for the swapped product volume.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/MeasureTheory/EuclideanSpace.lean#L27-L28

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace EuclideanSpace

/-- The coordinates of a point of the Euclidean plane, listed second coordinate first. -/
def finTwoCoordinatesSwap (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  (p 1, p 0)

end EuclideanSpace


