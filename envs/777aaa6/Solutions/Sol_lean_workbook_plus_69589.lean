-- Prove2me | solution 1 for lean_workbook_plus_69589
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:59.759711+00:00
-- url     : https://prove2.me/submissions/49a4e6f5-c41f-40e6-88b2-3163c7096317

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x a b : ℤ) (ha : a = x^3 - 1) (hb : b = (x + 1)^3 + 1) :
  a^3 + b^3 = (a + b)^3 ↔ a * b * (a + b) = 0 := by
  intros
  grind
