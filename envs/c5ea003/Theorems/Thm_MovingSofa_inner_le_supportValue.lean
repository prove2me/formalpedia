-- Prove2me | Theorems.Thm_MovingSofa_inner_le_supportValue
-- name    : MovingSofa.inner_le_supportValue
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-04T23:41:34.420364+00:00
-- url     : https://prove2.me/theorems/d45008a1-081e-4539-84f9-afa2070ece04
-- title:
--   Support value dominates inner products
-- statement:
--   Let $ be a planar convex body, $ a point of $, and import Mathlib.Analysis.Convex.Body
--   import Mathlib.Analysis.InnerProductSpace.Basic
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import Mathlib.Analysis.SpecialFunctions.Complex.Arg
--   import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
--   import Definitions.Def_MovingSofa_Geometry_Basic
--   import Definitions.Def_MovingSofa_Geometry_Plane
--   import Definitions.Def_MovingSofa_Geometry_Basic
--   noncomputable section
--
--   namespace MovingSofa
--
--   theorem inner_le_supportValue (K : ConvexBody Point) {p : Point}
--       (hp : p ∈ K) (t : Real.Angle) : inner ℝ p (normalVector t) ≤ supportValue K t := by sorry
--
--   end MovingSofa
--   $ an angle. Then the inner product of $ with the unit normal at import Mathlib.Analysis.Convex.Body
--   import Mathlib.Analysis.InnerProductSpace.Basic
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import Mathlib.Analysis.SpecialFunctions.Complex.Arg
--   import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
--   import Definitions.Def_MovingSofa_Geometry_Basic
--   import Definitions.Def_MovingSofa_Geometry_Plane
--   import Definitions.Def_MovingSofa_Geometry_Basic
--   noncomputable section
--
--   namespace MovingSofa
--
--   theorem inner_le_supportValue (K : ConvexBody Point) {p : Point}
--       (hp : p ∈ K) (t : Real.Angle) : inner ℝ p (normalVector t) ≤ supportValue K t := by sorry
--
--   end MovingSofa
--   $ is at most the support value of $ at import Mathlib.Analysis.Convex.Body
--   import Mathlib.Analysis.InnerProductSpace.Basic
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import Mathlib.Analysis.SpecialFunctions.Complex.Arg
--   import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
--   import Definitions.Def_MovingSofa_Geometry_Basic
--   import Definitions.Def_MovingSofa_Geometry_Plane
--   import Definitions.Def_MovingSofa_Geometry_Basic
--   noncomputable section
--
--   namespace MovingSofa
--
--   theorem inner_le_supportValue (K : ConvexBody Point) {p : Point}
--       (hp : p ∈ K) (t : Real.Angle) : inner ℝ p (normalVector t) ≤ supportValue K t := by sorry
--
--   end MovingSofa
--   $. This is the defining inequality of the support function.
-- source:
--   https://github.com/deancureton/MovingSofa

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Definitions.Def_MovingSofa_Geometry_Basic
import Definitions.Def_MovingSofa_Geometry_Plane
import Definitions.Def_MovingSofa_Geometry_Basic
noncomputable section

namespace MovingSofa

theorem inner_le_supportValue (K : ConvexBody Point) {p : Point}
    (hp : p ∈ K) (t : Real.Angle) : inner ℝ p (normalVector t) ≤ supportValue K t := by sorry

end MovingSofa
