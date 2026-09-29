-- Prove2me | solution 1 for lean_workbook_plus_58412
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:29.284314+00:00
-- url     : https://prove2.me/submissions/67b4329e-7a34-4d69-9f96-d45b12faa7be

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (h : a + b + c ≥ 3) : 6 / (a + b + c - 1) ≤ 3 := by
  exact (div_le_iff₀ (show 0 < a+b+c-1 by linarith)).2 (by linarith)
