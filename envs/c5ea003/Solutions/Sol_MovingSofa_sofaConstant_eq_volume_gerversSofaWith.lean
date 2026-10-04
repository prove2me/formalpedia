-- Prove2me | solution 1 for MovingSofa.sofaConstant_eq_volume_gerversSofaWith
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T13:58:17.972582+00:00
-- url     : https://prove2.me/submissions/ddb19613-c3ad-462b-8e3b-720b25dad4dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MovingSofa_Basic
import Theorems.Thm_MovingSofa_volume_le_volume_gerversSofaWith
import Theorems.Thm_MovingSofa_isMovingSofa_gerversSofaWith

set_option autoImplicit false

open MovingSofa MeasureTheory
open scoped EuclideanGeometry Real ENNReal

theorem solution (A B phi theta : ℝ)
    (h : GerversSofa.ABphiThetaSpec A B phi theta) :
    sofaConstant = volume (gerversSofaWith A B phi theta) := by
  unfold sofaConstant
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    exact MovingSofa.volume_le_volume_gerversSofaWith A B phi theta h s hs
  · obtain ⟨m, hm⟩ := MovingSofa.isMovingSofa_gerversSofaWith A B phi theta h
    refine le_iSup_of_le (gerversSofaWith A B phi theta)
      (le_iSup_of_le (⟨m, hm⟩ : ∃ m, IsMovingSofa (gerversSofaWith A B phi theta) m) le_rfl)
