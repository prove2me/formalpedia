-- Prove2me | solution 1 for lean_workbook_plus_54147
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:47.917732+00:00
-- url     : https://prove2.me/submissions/6d6910e6-c988-4dc9-bc91-2d5940cb4172

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (M x: ℝ) (g : ℝ → ℝ) (h₁ : |g x - M| < |M| / 2) : |g x| > |M| / 2 := by
  intros
  grind
