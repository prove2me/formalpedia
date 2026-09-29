-- Prove2me | solution 1 for lean_workbook_plus_15889
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:48.473074+00:00
-- url     : https://prove2.me/submissions/8c5a2858-21f3-4f2b-a03c-3b060bde0ba7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (α β : ℝ) (h₁ : α = (1 + Real.sqrt 5) / 2) (h₂ : β = (1 - Real.sqrt 5) / 2) : α + β = 1 ∧ α - β = Real.sqrt 5 := by
  intros
  grind
