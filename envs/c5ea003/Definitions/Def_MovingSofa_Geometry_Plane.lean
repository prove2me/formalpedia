-- Prove2me | Definitions.Def_MovingSofa_Geometry_Plane
-- name    : MovingSofa_Geometry_Plane
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-10-04T22:32:26.381228+00:00
-- url     : https://prove2.me/theorems/cce1f035-68ca-4b7b-87d5-1b5f5f09f0c7
-- title:
--   The Euclidean plane as coordinate pairs
-- statement:
--   The Euclidean plane, formalized as real coordinate pairs with the standard inner product.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Geometry/Plane.lean

import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MovingSofa
abbrev Point := EuclideanSpace ℝ (Fin 2)

end MovingSofa


