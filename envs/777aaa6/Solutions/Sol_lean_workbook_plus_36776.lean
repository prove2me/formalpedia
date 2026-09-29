-- Prove2me | solution 1 for lean_workbook_plus_36776
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:31.801191+00:00
-- url     : https://prove2.me/submissions/2d43b0fa-9df2-4767-b067-d497c1bfb30c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y a b : ℝ) : a - b = (3 * x ^ 2 + 7 * x * y + 2 * y ^ 2 - (2 * x ^ 2 + 7 * x * y + 3 * y ^ 2)) / ((2 * x + y) * (3 * x + y)) → a - b = (x ^ 2 - y ^ 2) / ((2 * x + y) * (3 * x + y)) := by
  intros
  grind
