-- Prove2me | solution 1 for lean_workbook_plus_47129
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:27.699888+00:00
-- url     : https://prove2.me/submissions/695d7c78-f89b-4676-b589-88e536e6f057

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℂ)
  (h₀ : (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a) = 1) :
  a^2 + b^2 + c^2 = 1 / (a + b + c) + a * b + b * c + c * a := by
  intros
  grind
