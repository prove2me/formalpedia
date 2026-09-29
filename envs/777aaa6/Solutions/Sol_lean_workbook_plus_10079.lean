-- Prove2me | solution 1 for lean_workbook_plus_10079
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:40.261144+00:00
-- url     : https://prove2.me/submissions/75627205-aef8-4292-bfaf-46da4dcd604b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 1 / Real.sqrt 10 = Real.sqrt 10 / 10 := by
  intros
  grind
