-- Prove2me | solution 1 for MovingSofa.volume_gerversSofaWith_le_sofaConstant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T15:15:42.22798+00:00
-- url     : https://prove2.me/submissions/83bf7057-3f36-4f34-8801-989e97e99de9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MovingSofa_Basic
import Theorems.Thm_MovingSofa_isMovingSofa_gerversSofaWith

set_option autoImplicit false

open MovingSofa MeasureTheory
open scoped EuclideanGeometry Real ENNReal

theorem solution (A B phi theta : ℝ)
    (h : GerversSofa.ABphiThetaSpec A B phi theta) :
    volume (gerversSofaWith A B phi theta) ≤ sofaConstant := by
  unfold sofaConstant
  obtain ⟨m, hm⟩ := MovingSofa.isMovingSofa_gerversSofaWith A B phi theta h
  refine le_iSup_of_le (gerversSofaWith A B phi theta) ?_
  exact le_iSup_of_le (⟨m, hm⟩ : ∃ m, IsMovingSofa (gerversSofaWith A B phi theta) m) le_rfl
