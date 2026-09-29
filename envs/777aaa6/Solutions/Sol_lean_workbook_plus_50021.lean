-- Prove2me | solution 1 for lean_workbook_plus_50021
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:25.822795+00:00
-- url     : https://prove2.me/submissions/abf2f9dd-af20-44be-acc7-fe74222087fb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a * c + b * d = 2) : (a * d - b * c) ^ 2 + 2 ≥ a * d + b * c := by
  intros
  nlinarith [sq_nonneg (a*b - c*d), sq_nonneg (a*c - b*d), sq_nonneg (a*d - b*c)]
