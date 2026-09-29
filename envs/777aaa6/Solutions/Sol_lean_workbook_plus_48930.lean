-- Prove2me | solution 1 for lean_workbook_plus_48930
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:26.967031+00:00
-- url     : https://prove2.me/submissions/02c38366-652e-477b-973f-630fe36a4b31

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℤ) : x^4 + 1 = (x^2 - √2*x + 1) * (x^2 + √2*x + 1) := by
  intros
  grind
