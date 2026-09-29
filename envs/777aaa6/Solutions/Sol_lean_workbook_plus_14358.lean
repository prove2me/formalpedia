-- Prove2me | solution 1 for lean_workbook_plus_14358
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:35.575189+00:00
-- url     : https://prove2.me/submissions/1a78572d-4411-47d8-9a1b-f0ba98f9d5e6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ x : ℝ, x >= -10 → (x^2 + 1) * (x + 7) + (x - 10)^2 >= 97 := by
  intro x hx
  have h := mul_nonneg (sq_nonneg (x - 1)) (show 0 ≤ x + 10 by linarith)
  nlinarith [h]
