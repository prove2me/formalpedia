-- Prove2me | solution 1 for lean_workbook_plus_8864
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:50.946718+00:00
-- url     : https://prove2.me/submissions/5c4fef44-0160-41fe-ae48-0af0fcc4bfd3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : (Real.sqrt 5 + 2) ^ 3 * (Real.sqrt 5 - 2) ^ 3 = 1 := by
  intros
  grind
