-- Prove2me | solution 1 for lean_workbook_plus_10616
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:19.72303+00:00
-- url     : https://prove2.me/submissions/9d4d177a-5f9d-4940-94f8-a6d1f4a52829

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ)
  (h₀ : c = -(a + b))
  (h₁ : a^2 + b^2 + c^2 = 1) :
  a * b = -1 / 2 + c^2 := by
  intros
  grind
