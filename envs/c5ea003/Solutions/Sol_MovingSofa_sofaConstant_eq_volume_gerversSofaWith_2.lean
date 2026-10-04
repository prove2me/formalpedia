-- Prove2me | solution 2 for MovingSofa.sofaConstant_eq_volume_gerversSofaWith
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T15:26:26.000273+00:00
-- url     : https://prove2.me/submissions/35c26090-6a94-4636-a5c1-874ccdb54d2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MovingSofa_Basic
import Theorems.Thm_MovingSofa_volume_le_volume_gerversSofaWith
import Theorems.Thm_MovingSofa_volume_gerversSofaWith_le_sofaConstant

set_option autoImplicit false

open MovingSofa MeasureTheory
open scoped EuclideanGeometry Real ENNReal

theorem solution (A B phi theta : ℝ)
    (h : GerversSofa.ABphiThetaSpec A B phi theta) :
    sofaConstant = volume (gerversSofaWith A B phi theta) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    exact MovingSofa.volume_le_volume_gerversSofaWith A B phi theta h s hs
  · exact MovingSofa.volume_gerversSofaWith_le_sofaConstant A B phi theta h
