-- Prove2me | solution 1 for lean_workbook_plus_9423
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:01:16.197359+00:00
-- url     : https://prove2.me/submissions/09575843-8c51-4390-b168-68a031ca351d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0) :
  1 / a + 1 / b = (a + b) / (a * b) := by
  rcases h₀ with ⟨ha,hb⟩
  field_simp
  <;> ring
