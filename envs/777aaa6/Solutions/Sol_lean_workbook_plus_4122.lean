-- Prove2me | solution 1 for lean_workbook_plus_4122
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:09.927092+00:00
-- url     : https://prove2.me/submissions/cacd7c79-7300-4ba1-8bac-2dc5cca908dd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℤ) : x^2 + y^2 = 2 * z^2 ↔ (x + y)^2 + (x - y)^2 = (2 * z)^2 := by
  intros
  grind
