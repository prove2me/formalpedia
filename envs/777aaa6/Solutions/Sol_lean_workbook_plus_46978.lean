-- Prove2me | solution 1 for lean_workbook_plus_46978
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:27.275386+00:00
-- url     : https://prove2.me/submissions/ec803071-5fdb-435b-bcd4-be08604579fc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) = a^3 + b^3 + c^3 + 2 * a * b * c + 1 ↔ a * b * c - 1 = a^3 + b^3 + c^3 + 3 * a * b * c - a * b * (a + b) - b * c * (b + c) - c * a * (c + a) := by
  intros
  grind
