-- Prove2me | solution 1 for lean_workbook_plus_51895
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:08:51.41136+00:00
-- url     : https://prove2.me/submissions/ef5973c4-97ef-4d79-a7de-4ccc841ece89

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ)
  (h₀ : x^2 - 2 * x - 48 = 0) :
  x = -6 ∨ x = 8 := by
  intros
  grind
