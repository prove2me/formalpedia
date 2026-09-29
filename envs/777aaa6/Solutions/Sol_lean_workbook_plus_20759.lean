-- Prove2me | solution 1 for lean_workbook_plus_20759
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:04.172721+00:00
-- url     : https://prove2.me/submissions/7ef5ff30-6e87-4a07-9d85-30defec6f3f9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) :
  (a / b) ^ 2 + (b / c) ^ 2 + (c / a) ^ 2 ≥
    1 / 3 * (a / b + b / c + c / a) ^ 2 := by
  nlinarith [sq_nonneg (a/b-b/c),sq_nonneg (b/c-c/a),sq_nonneg (c/a-a/b)]
