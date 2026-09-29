-- Prove2me | Theorems.Thm_mme_CW_q5_fourth_Z_grade_fiber_card
-- name    : mme_CW_q5_fourth_Z_grade_fiber_card
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T18:53:00.649994+00:00
-- url     : https://prove2.me/theorems/a267a620-4707-4b29-be6b-0e1a45116889
-- title:
--   Exact cardinalities of q=5 fourth Z-grade fibers
-- statement:
--   Every canonical grade-k fourth Z-alphabet has exactly fiberSize(k,a) coordinates of left-square grade a. This also holds for universe-lifted canonical basis indices.
-- source:
--   Canonical fourth CW basis and released original q=5 DWZ global Z-profile data.

import Definitions.Def_mme_CW_q5_fourth_boundary_alphabet_data
open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.CWFourthBoundaryQ5
universe u
set_option autoImplicit false

theorem mme_CW_q5_fourth_Z_grade_fiber_card (k : Fin 9) (a : Fin 5) :
    Fintype.card {p : LiftedCoarseCoordinate.{u} 5 k //
      cwSquarePairGrade 5 p.down.val.1 = a} = fiberSize k a  := by sorry
