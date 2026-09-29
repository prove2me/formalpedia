-- Prove2me | solution 1 for lean_workbook_plus_52547
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:14.208801+00:00
-- url     : https://prove2.me/submissions/49cf04aa-012a-416b-ad1f-8f4777d0b0f2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 3*x - 5 < 10 ↔ x < 5 := by
  intros
  grind
