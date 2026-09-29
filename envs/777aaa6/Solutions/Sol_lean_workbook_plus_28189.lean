-- Prove2me | solution 1 for lean_workbook_plus_28189
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:53.055318+00:00
-- url     : https://prove2.me/submissions/03699825-d414-44f9-8d8c-0ecbce6e868d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (g : ℝ → ℝ) (g_of : ∀ x, x ≠ 0 → g x = 3 * x + 21) (g_on : g 0 = 21) : ∀ x, g x = 3 * x + 21 := by
  intros
  grind
