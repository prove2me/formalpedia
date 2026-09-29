-- Prove2me | solution 1 for lean_workbook_plus_8211
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:09.076265+00:00
-- url     : https://prove2.me/submissions/5d660671-b541-4def-8100-2ff69d0bdd7f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : x - y = 7) (h₂ : x * y = 8) : x^2 - y^2 = 63 ∨ x^2 - y^2 = -63 := by
  intros
  grind
