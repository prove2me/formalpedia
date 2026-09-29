-- Prove2me | solution 1 for lean_workbook_plus_10773
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:32.157022+00:00
-- url     : https://prove2.me/submissions/14d0a2f7-568d-48f1-ae10-99c8d51568ed

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : (Real.sqrt (2 - Real.sqrt 2)) / 2 = (Real.sqrt 2 / 2) * Real.sqrt (1 - Real.sqrt 2 / 2) := by
  have hi : 2-Real.sqrt 2 = 2*(1-Real.sqrt 2/2) := by ring
  rw [hi,Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num)]
  ring
