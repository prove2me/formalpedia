-- Prove2me | solution 1 for lean_workbook_plus_17088
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:59.367886+00:00
-- url     : https://prove2.me/submissions/3c51d54f-b8db-4f91-873a-0a66a73c9dd4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (f : ℝ → ℝ) (h₁ : f = fun x => a * x ^ 4 - b * x ^ 2 + x + 5) (h₂ : f (-3) = 2) : f 3 = 8 := by
  intros
  grind
