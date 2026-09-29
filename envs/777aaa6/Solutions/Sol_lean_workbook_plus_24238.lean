-- Prove2me | solution 1 for lean_workbook_plus_24238
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:04.730712+00:00
-- url     : https://prove2.me/submissions/da97bb8f-702b-48d9-876c-9e78f14b586e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℚ) (h₁ : a = 1 / 2) (h₂ : b = 4 / 5) (h₃ : c = 10 / 11) (h₄ : d = 22 / 23) : a * b * c * d = 8 / 23 := by
  intros
  grind
