-- Prove2me | solution 1 for lean_workbook_plus_54844
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:12.217001+00:00
-- url     : https://prove2.me/submissions/5382cf61-443e-4367-913c-229530020ec5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b: ℤ) : a + b + 1 = a * b - 2 ↔ (a-1) * (b-1) = 4 := by
  intros
  grind
