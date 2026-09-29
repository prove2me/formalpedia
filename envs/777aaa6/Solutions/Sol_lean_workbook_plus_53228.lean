-- Prove2me | solution 1 for lean_workbook_plus_53228
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:03.797128+00:00
-- url     : https://prove2.me/submissions/e1984341-3e45-43ac-a69a-2292121196a4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {x y z : ℚ} (h : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0) (habc : x * y * z ≠ 0) (h : 1 / x ^ 2 + 1 / y ^ 2 = 1 / z ^ 2) : (x * z) ^ 2 + (y * z) ^ 2 = (x * y) ^ 2 := by
  intros
  grind
