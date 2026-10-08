-- Prove2me | Theorems.Thm_MovingSofa_inner_le_supportValue_of_isCompact
-- name    : MovingSofa.inner_le_supportValue_of_isCompact
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-10-05T00:43:22.003183+00:00
-- url     : https://prove2.me/theorems/224195b6-3e62-4bc5-b603-811a2f186633
-- title:
--   Support inequality on compacta
-- statement:
--   On a compact set, inner products against the frame normal are bounded by the support value.
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

theorem inner_le_supportValue_of_isCompact {s : Set Point}
    (hs : IsCompact s) {p : Point} (hp : p ∈ s) (a : Real.Angle) :
    inner ℝ p (normalVector a) ≤ supportValue s a := by sorry

end MovingSofa
