-- Prove2me | solution 1 for lean_workbook_plus_56265
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:56.446361+00:00
-- url     : https://prove2.me/submissions/c5bd4e90-dca4-4553-bcbd-6b501522f449

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c x y z : ℝ) (ha : a = 1 + x) (hb : b = 1 + y) (hc : c = 1 + z) (hx : x ≥ -1) (hy : y ≥ -1) (hz : z ≥ -1) : a^2 + b^2 + c^2 + 2 * a * b * c + 3 - (1 + a) * (1 + b) * (1 + c) = x^2 + y^2 + z^2 + x * y * z := by
  intros
  grind
