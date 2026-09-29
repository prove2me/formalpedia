-- Prove2me | solution 1 for lean_workbook_plus_30282
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:47.723391+00:00
-- url     : https://prove2.me/submissions/f8f95674-8ab2-48a0-bf8f-28a9372e034f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℂ) (h : x + y + z = 0) : x^3 + y^3 + z^3 = 3 * x * y * z := by
  intros
  grind
