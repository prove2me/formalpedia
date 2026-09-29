-- Prove2me | solution 1 for lean_workbook_plus_386
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:07.480972+00:00
-- url     : https://prove2.me/submissions/69a84139-6ddd-48e1-8ed1-8989770d44ae

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x t : ℂ) : (1 + 2 * x - t ^ 2) * t - x ^ 2 + x + x * (2 * x - t ^ 2) = 0 ↔ x = t ^ 2 - t ∨ x = -t - 1 := by
  have he : (1+2*x-t^2)*t-x^2+x+x*(2*x-t^2) = (x-t^2+t)*(x+t+1) := by ring
  rw [he, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; linear_combination h
    · right; linear_combination h
  · rintro (rfl | rfl) <;> ring_nf <;> simp
