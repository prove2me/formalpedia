-- Prove2me | solution 1 for mme_CW_q5_fourth_Z_grade_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T18:54:58.668842+00:00
-- url     : https://prove2.me/submissions/1b81f1cc-3b7b-478d-b35b-c9bfc67b8bb1

import Definitions.Def_mme_CW_q5_fourth_boundary_alphabet_data
import Mathlib.Tactic
open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.CWFourthBoundaryQ5
universe u
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem solution (k : Fin 9) (a : Fin 5) :
    Fintype.card {p : LiftedCoarseCoordinate.{u} 5 k //
      cwSquarePairGrade 5 p.down.val.1 = a} = fiberSize k a := by
  classical
  let e : {p : LiftedCoarseCoordinate.{u} 5 k // cwSquarePairGrade 5 p.down.val.1 = a} ≃
      {p : CoarseCoordinate 5 k // cwSquarePairGrade 5 p.val.1 = a} :=
    Equiv.ulift.subtypeEquiv (by intro p; rfl)
  rw [Fintype.card_congr e]
  clear e
  revert a k
  decide +kernel
