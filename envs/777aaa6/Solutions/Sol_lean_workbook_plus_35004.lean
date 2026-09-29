-- Prove2me | solution 1 for lean_workbook_plus_35004
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:21.290739+00:00
-- url     : https://prove2.me/submissions/fdcaf886-b287-4bd7-811b-ab5555552078

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * a^2 + b * b^2 + c * c^2 ≥ a * c^2 + b * a^2 + c * b^2 := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
