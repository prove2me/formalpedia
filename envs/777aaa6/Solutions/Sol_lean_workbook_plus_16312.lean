-- Prove2me | solution 1 for lean_workbook_plus_16312
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:56.092517+00:00
-- url     : https://prove2.me/submissions/412fb8dd-751c-4de9-ae72-5d6fb71ec619

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℚ) (h₁ : a = 8 / 4) (h₂ : b = 8 / 3) (h₃ : c = 8 / 2) : a < b ∧ b < c := by
  intros
  grind
