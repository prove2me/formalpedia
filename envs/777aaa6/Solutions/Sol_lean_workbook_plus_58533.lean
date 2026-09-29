-- Prove2me | solution 1 for lean_workbook_plus_58533
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:53.227149+00:00
-- url     : https://prove2.me/submissions/79fda1b8-88d4-4c30-92fb-3b084c2f7e53

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p : ℤ → ℤ) (h : ∀ x y : ℤ, x * p x = y * p y) : p 1 = 0 := by
  have h10 := h 1 0
  simpa using h10
