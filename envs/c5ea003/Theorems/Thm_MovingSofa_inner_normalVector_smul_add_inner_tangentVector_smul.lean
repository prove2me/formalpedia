-- Prove2me | Theorems.Thm_MovingSofa_inner_normalVector_smul_add_inner_tangentVector_smul
-- name    : MovingSofa.inner_normalVector_smul_add_inner_tangentVector_smul
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-10-04T23:41:52.905058+00:00
-- url     : https://prove2.me/theorems/19ceac38-6848-48df-9542-a0239cf91c47
-- title:
--   Frame decomposition of a plane vector
-- statement:
--   Every plane vector splits along the rotating orthonormal frame into its normal and tangential scalar multiples. This is the coordinate identity behind all frame computations.
-- source:
--   https://github.com/deancureton/MovingSofa

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Definitions.Def_MovingSofa_Geometry_Basic
import Definitions.Def_MovingSofa_Geometry_Basic
noncomputable section

namespace MovingSofa

theorem inner_normalVector_smul_add_inner_tangentVector_smul (p : Point) (t : Real.Angle) :
    inner ℝ p (normalVector t) • normalVector t +
      inner ℝ p (tangentVector t) • tangentVector t = p := by sorry

end MovingSofa
