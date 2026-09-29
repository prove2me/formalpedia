-- Prove2me | solution 1 for lean_workbook_plus_14615
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:07.668048+00:00
-- url     : https://prove2.me/submissions/65ac1b8b-5225-4a99-b693-a9e4d96434e3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (h₁ : a = 2112) (h₂ : b = 2021) (h₃ : c = 169) : (a - b) ^ 2 / c = 49 := by
  intros
  grind
