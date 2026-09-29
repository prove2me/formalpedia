-- Prove2me | solution 1 for lean_workbook_plus_47221
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:20.578031+00:00
-- url     : https://prove2.me/submissions/c5cbd083-0e27-46df-9a31-4f2feb288163

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution :
  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a + b) / c + (b + c) / a + (c + a) / b - 6 ≥ 0 := by
  intro a b c h
  rcases h with ⟨ha,hb,hc⟩
  have hi : (a+b)/c+(b+c)/a+(c+a)/b-6 = (a*(b-c)^2+b*(c-a)^2+c*(a-b)^2)/(a*b*c) := by
    field_simp
    ring
  rw [hi]
  positivity
