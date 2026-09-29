-- Prove2me | solution 1 for lean_workbook_plus_59293
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:08.386817+00:00
-- url     : https://prove2.me/submissions/945912e3-7d49-4845-9e87-027e70add304

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (hx : x = (x + y) / 2) (hy : y = Real.sqrt (x * y)) : x = y := by
  intros
  grind
