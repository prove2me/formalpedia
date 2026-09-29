-- Prove2me | solution 1 for lean_workbook_plus_42806
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:42.111018+00:00
-- url     : https://prove2.me/submissions/1392b38b-279e-4087-9af6-876e6d230a55

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (p : ℝ)
  (h₀ : p = 1 / 2 + 1 / 2 * (1 - p)) :
  p = 2 / 3 := by
  linarith
