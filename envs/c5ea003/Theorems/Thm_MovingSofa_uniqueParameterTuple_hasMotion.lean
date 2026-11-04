-- Prove2me | Theorems.Thm_MovingSofa_uniqueParameterTuple_hasMotion
-- name    : MovingSofa.uniqueParameterTuple_hasMotion
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:34:16.686816+00:00
-- url     : https://prove2.me/theorems/96908aff-ed6a-4244-96d2-96b426d494de
-- title:
--   A unique Gerver parameter tuple admits a hallway motion
-- statement:
--   For a quadruple that satisfies Gerver's four equations and is the unique such quadruple, the sofa defined by those parameters admits a continuous rigid motion that stays within the width-one L-shaped hallway from the horizontal arm to the vertical arm.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Gerver/Motion.lean

import Definitions.Def_MovingSofa_Basic
open MovingSofa
open scoped EuclideanGeometry Real

namespace MovingSofa
theorem uniqueParameterTuple_hasMotion
    (q : ℝ × ℝ × ℝ × ℝ)
    (hq : GerversSofa.ABphiThetaSpec q.1 q.2.1 q.2.2.1 q.2.2.2)
    (hu : ∀ q' : ℝ × ℝ × ℝ × ℝ,
      GerversSofa.ABphiThetaSpec q'.1 q'.2.1 q'.2.2.1 q'.2.2.2 → q' = q) :
    ∃ m, IsMovingSofa (gerversSofaWith q.1 q.2.1 q.2.2.1 q.2.2.2) m := by sorry
end MovingSofa
