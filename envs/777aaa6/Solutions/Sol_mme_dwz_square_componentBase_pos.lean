-- Prove2me | solution 1 for mme_dwz_square_componentBase_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:11:03.562057+00:00
-- url     : https://prove2.me/submissions/c7b2e2c3-3a1b-40d3-b2e1-311479fd17dd

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data

open MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true

theorem solution (tau : ℝ) (s : Fin 15) :
    0 < componentBase tau s := by
  fin_cases s <;>
    simp [componentBase, splitA, splitB] <;>
    positivity

