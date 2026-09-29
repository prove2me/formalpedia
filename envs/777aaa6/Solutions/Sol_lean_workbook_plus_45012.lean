-- Prove2me | solution 1 for lean_workbook_plus_45012
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:58.097293+00:00
-- url     : https://prove2.me/submissions/de3170a5-b26a-4253-aaef-0ddc9352d13d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x/8 + x/12 + x/6 = 2 ↔ x = 16/3 := by
  intros
  grind
