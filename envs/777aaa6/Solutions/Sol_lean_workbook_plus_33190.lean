-- Prove2me | solution 1 for lean_workbook_plus_33190
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:54.119491+00:00
-- url     : https://prove2.me/submissions/2babe5ff-78d9-41d9-ad8f-f9458bfec79c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ)
  (h₀ : x - y = 32 * (z - 1))
  (h₁ : x - y - (y - 72) = 35 * (z - 2))
  (h₂ : x - (y - 72) = 40 * (z - 1)) :
  x = 368 ∧ y = 80 ∧ z = 10 := by
  intros
  grind
