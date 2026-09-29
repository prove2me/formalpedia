-- Prove2me | solution 1 for lean_workbook_plus_9027
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:11:11.66058+00:00
-- url     : https://prove2.me/submissions/a0ba1fd7-b08f-4341-9d8f-80b560e9f4bb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p q r a b c α : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x ∈ Set.Icc (-1) 1)
  (h₁ : f (-1) = p)
  (h₂ : f 0 = q)
  (h₃ : f 1 = r)
  (h₄ : a = (p + r - 2 * q) / 2)
  (h₅ : b = (r - p) / 2)
  (h₆ : c = q)
  (h₇ : 6 * abs a + abs b + 9 * abs c = α) :
  3 * abs (p + r - 2 * q) + 1 / 2 * abs (r - p) + 9 * abs q = α := by
  intros
  grind
