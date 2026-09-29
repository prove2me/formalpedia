-- Prove2me | solution 1 for lean_workbook_plus_35822
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:44.857778+00:00
-- url     : https://prove2.me/submissions/eec90f1e-278c-4b64-b91a-c54a60ba87b8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ → ℝ) (h₁ : ∀ x, f x = x^3) : Function.Injective f := by
  intro x y h
  rw [h₁ x,h₁ y] at h
  exact (Odd.strictMono_pow (by decide : Odd 3)).injective h
