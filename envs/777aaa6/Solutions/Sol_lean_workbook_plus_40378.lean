-- Prove2me | solution 1 for lean_workbook_plus_40378
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:40.558717+00:00
-- url     : https://prove2.me/submissions/753df934-5325-4b16-834e-a383135bc485

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (t : ℂ) : (1 - t)^5 = t ↔ -t^5 + 5 * t^4 - 10 * t^3 + 10 * t^2 - 6 * t + 1 = 0 := by
  intros
  grind
