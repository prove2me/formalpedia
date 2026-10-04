-- Prove2me | Theorems.Thm_MovingSofa_volume_gerversSofaWith_le_sofaConstant
-- name    : MovingSofa.volume_gerversSofaWith_le_sofaConstant
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-03T15:15:39.756894+00:00
-- url     : https://prove2.me/theorems/e6d63620-daf7-441a-8ab6-e5818a5b66b4
-- title:
--   Gerver's area attains the sofa constant
-- statement:
--   Gerver's shape witnesses attainment: its area lies below the supremum over all moving sofas, via the movability witness. Source: Gerver/Motion.lean volume_gerversSofa_le_sofaConstant, parameterized over spec solutions.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Gerver/Motion.lean#L47-L49

import Definitions.Def_MovingSofa_Basic
open MovingSofa MeasureTheory
open scoped EuclideanGeometry Real ENNReal

namespace MovingSofa

theorem volume_gerversSofaWith_le_sofaConstant (A B phi theta : ℝ)
    (h : GerversSofa.ABphiThetaSpec A B phi theta) :
    volume (gerversSofaWith A B phi theta) ≤ sofaConstant := by sorry

end MovingSofa
