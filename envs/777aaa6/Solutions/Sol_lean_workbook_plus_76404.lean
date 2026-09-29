-- Prove2me | solution 1 for lean_workbook_plus_76404
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:47.782042+00:00
-- url     : https://prove2.me/submissions/73ba8200-495a-42a2-a639-490683ca331e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : x + y = 5/2) (h₂ : x^2 + y^2 = 13/4) : x^5 + y^5 = 275/32 := by
  intros
  grind
