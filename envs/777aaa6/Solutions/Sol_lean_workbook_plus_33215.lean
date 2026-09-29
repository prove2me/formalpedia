-- Prove2me | solution 1 for lean_workbook_plus_33215
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:29.4582+00:00
-- url     : https://prove2.me/submissions/3d84452d-2895-4cd3-8b73-8b23ca9d4841

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c x₁ x₂ x₃ : ℂ) (h₁ : x₁ * x₂ = b * c) (h₂ : x₂ * x₃ = a * c) : x₂ * (x₁ - x₃) = c * (b - a) := by
  intros
  grind
