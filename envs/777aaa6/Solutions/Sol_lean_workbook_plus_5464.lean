-- Prove2me | solution 1 for lean_workbook_plus_5464
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:39.234463+00:00
-- url     : https://prove2.me/submissions/c4a6cb00-9e11-4119-827e-a99bd21e6285

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (l₁ l₂ l₃ : ℝ) (h₁ : l₁ = 100) (h₂ : l₂ = 30) (h₃ : l₃ = 50) : l₁ * l₂ * l₃ = 150000 := by
  intros
  grind
