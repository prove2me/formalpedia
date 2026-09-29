-- Prove2me | solution 1 for lean_workbook_plus_5709
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:29.315927+00:00
-- url     : https://prove2.me/submissions/ceee1362-4ff2-474e-b017-737402076a56

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℤ) : (16*x + 56)*(2*x^2 + 14*x + 56) = 4*y^3 ↔ (2*x + 7)^3 + 63*(2*x + 7) = y^3 := by
  intros
  grind
