-- Prove2me | solution 1 for lean_workbook_plus_55689
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:51.651223+00:00
-- url     : https://prove2.me/submissions/02136a92-54f7-48f9-8caf-04328fa03e11

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : (4 ^ 545 + 545 ^ 4) % 6 = 5 := by
  intros
  rfl
