-- Prove2me | solution 1 for lean_workbook_plus_48740
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:58.356432+00:00
-- url     : https://prove2.me/submissions/4bc57a24-f6c5-40a4-9926-5df4c466f7e0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 2005 = 41^2 + 18^2 → 2005^2005 = (41 * 2005^1002)^2 + (18 * 2005^1002)^2 := by
  intros
  rfl
