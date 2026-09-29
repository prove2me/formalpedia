-- Prove2me | solution 1 for lean_workbook_plus_41586
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:18.097082+00:00
-- url     : https://prove2.me/submissions/e28c69d6-9b69-4b6c-835c-fe7cdb2bb713

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habcd : a * b * c * d = 1) (h : a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2 ≤ 2 * (b * c + d * a)) : a * b - c * d ≤ 1 := by
  intros
  nlinarith [sq_nonneg (a*b - c*d), sq_nonneg (a*c - b*d), sq_nonneg (a*d - b*c)]
