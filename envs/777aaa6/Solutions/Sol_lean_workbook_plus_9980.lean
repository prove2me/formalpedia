-- Prove2me | solution 1 for lean_workbook_plus_9980
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:56.620203+00:00
-- url     : https://prove2.me/submissions/d7796e26-50f5-49cd-9d6b-5bd316b0a321

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x k : ℂ) : (x^4 - 2 * k * x^2 - x + k^2 - k = 0) ↔ (k = x^2 + x + 1 ∨ k = x^2 - x) := by
  intros
  grind
