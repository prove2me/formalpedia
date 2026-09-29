-- Prove2me | solution 1 for lean_workbook_plus_35095
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:18.243509+00:00
-- url     : https://prove2.me/submissions/9b6b8eac-6364-4a77-b2dc-499145312b4d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (r : ℚ) (hr : 0 < r) : (r^2 + 1) / r ≤ 1 → (r^2 + 2) / r ≤ 2 := by
  intro h
  have hh := (div_le_iff₀ hr).mp h
  exfalso
  nlinarith [sq_nonneg (r-1/2)]
