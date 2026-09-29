-- Prove2me | solution 1 for lean_workbook_plus_18331
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:09.80589+00:00
-- url     : https://prove2.me/submissions/187f039c-e8dc-4654-91d9-fc8c312bba54

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) :
  2 * (a^2 + b^2 + c^2) * (a + b + c) = 3 * (a * b + b * c + c * a) * (a + b + c) ↔
  2 * (a^3 + b^3 + c^3) = a * b * (a + b) + b * c * (b + c) + c * a * (c + a) + 9 * a * b * c := by
  intros
  grind
