-- Prove2me | solution 1 for lean_workbook_plus_42647
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:33.546019+00:00
-- url     : https://prove2.me/submissions/a24617f4-abcd-4eb1-a6a4-c2a5af57c0dd

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x k : ℝ)
  (h₀ : x < 0)
  (h₁ : x + k < 0)
  (h₂ : k ≠ 0) :
  |x + k| ≠ -x + k := by
  rw [abs_of_neg h₁]
  intro h
  apply h₂
  linarith
