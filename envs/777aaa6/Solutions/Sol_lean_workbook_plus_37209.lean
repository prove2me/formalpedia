-- Prove2me | solution 1 for lean_workbook_plus_37209
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:32.449388+00:00
-- url     : https://prove2.me/submissions/7111317b-5897-4b89-814f-6bcfa4361c8a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ⌊Real.sqrt 2021⌋ = 44 := by
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
