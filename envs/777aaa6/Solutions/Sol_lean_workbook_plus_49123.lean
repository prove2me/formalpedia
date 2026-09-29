-- Prove2me | solution 1 for lean_workbook_plus_49123
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:12.739488+00:00
-- url     : https://prove2.me/submissions/d07954ab-0f66-4313-9917-3deefc137c50

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : 1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2 = (1 / (a - b) + 1 / (b - c) + 1 / (c - a)) ^ 2 := by
  intros
  grind
