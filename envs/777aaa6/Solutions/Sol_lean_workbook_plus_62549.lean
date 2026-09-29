-- Prove2me | solution 1 for lean_workbook_plus_62549
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:16.933749+00:00
-- url     : https://prove2.me/submissions/2791d1d5-dc5c-4fe6-811b-1a8a5c4588f6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c x y z : ℝ) (h1 : a + b = x) (h2 : b + c = y) (h3 : a + c = z) : (a - b) * (b - c) * (c - a) / (a + b) / (b + c) / (a + c) = (z - y) * (x - z) * (y - x) / (x * y * z) := by
  intros
  grind
