-- Prove2me | solution 1 for lean_workbook_plus_21271
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:38.599315+00:00
-- url     : https://prove2.me/submissions/20f1ec1f-16a7-438c-9f16-d206b0a1ef97

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : IsConnected (Set.Icc (0 : ℝ) 1) := by
  exact isConnected_Icc (by norm_num : (0:ℝ) ≤ 1)
