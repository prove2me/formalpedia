-- Prove2me | solution 1 for lean_workbook_plus_20550
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:36.588299+00:00
-- url     : https://prove2.me/submissions/dff1fb2c-0a5a-4376-9f9f-671ec65d590d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : 2 * |a + b + c| ≤ |a + b| + |b + c| + |c + a| := by
  intros
  grind
