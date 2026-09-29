-- Prove2me | solution 1 for lean_workbook_plus_42537
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:02.736282+00:00
-- url     : https://prove2.me/submissions/ccbe980f-6b9b-410b-ae61-62bbb1edbedf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x j : ℝ)
  (h₀ : x ≠ 1)
  (h₁ : j ≠ 0) :
  1 / (1 - x) - x = 1 + x^2 / (1 - x) := by
  intros
  grind
