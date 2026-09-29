-- Prove2me | solution 1 for lean_workbook_plus_8411
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:38.30504+00:00
-- url     : https://prove2.me/submissions/bd7e048f-9dc1-4657-8b74-fb823812daec

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (f : ℝ → ℝ) (h₁ : f = fun x => a * x + b * x + x + 5) : f (-4) = 3 → f 4 = 7 := by
  intros
  grind
