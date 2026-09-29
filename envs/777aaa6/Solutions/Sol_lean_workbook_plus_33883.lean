-- Prove2me | solution 1 for lean_workbook_plus_33883
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:23.912316+00:00
-- url     : https://prove2.me/submissions/beb8a40f-10ac-4e06-8e61-079df6de7f69

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℤ} (h : a + b + c = 0) : a^5 + b^5 + c^5 = -5 * a * b * (a + b) * (a^2 + a * b + b^2) := by
  intros
  grind
