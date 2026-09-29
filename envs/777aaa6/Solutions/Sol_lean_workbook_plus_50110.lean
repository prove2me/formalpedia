-- Prove2me | solution 1 for lean_workbook_plus_50110
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:45.75279+00:00
-- url     : https://prove2.me/submissions/282a93f3-ef99-4ca4-acb9-b64019a80487

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (m n : ℂ)
  (h₀ : m^3 + n^3 + 3 * m * n = 1) :
  (m + n - 1) * (m^2 + n^2 - m * n + m + n + 1) = 0 := by
  intros
  grind
