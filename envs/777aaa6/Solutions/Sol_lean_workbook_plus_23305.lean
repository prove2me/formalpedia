-- Prove2me | solution 1 for lean_workbook_plus_23305
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:58.981088+00:00
-- url     : https://prove2.me/submissions/5af9440c-2120-4ded-85d9-0bd11eac9f3d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ)
  (h₀ : x ≠ 0)
  (h₁ : y = (x^2 - z^2) / x) :
  x^2 - z^2 = x * y := by
  rw [h₁]
  field_simp
  <;> ring
