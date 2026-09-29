-- Prove2me | solution 1 for lean_workbook_plus_59732
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:24.43998+00:00
-- url     : https://prove2.me/submissions/184e00cd-fd2c-472f-8178-8587d670c737

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  3 / Real.sqrt 7 - 2 / Real.sqrt 6 = (9 * Real.sqrt 7 - 7 * Real.sqrt 6) / 21 := by
  intros
  grind
