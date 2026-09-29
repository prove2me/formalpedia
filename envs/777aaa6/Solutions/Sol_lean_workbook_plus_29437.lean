-- Prove2me | solution 1 for lean_workbook_plus_29437
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:30.540179+00:00
-- url     : https://prove2.me/submissions/d31bfb2f-d85f-469f-9033-9f327321612a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (h₁ : a = 30) (h₂ : b = 1 / 2) (h₃ : c = 2 / 3) (h₄ : d = 4 / 5) : a * b * c * d = 8 := by
  intros
  grind
