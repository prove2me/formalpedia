-- Prove2me | solution 1 for lean_workbook_plus_14673
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:53.297651+00:00
-- url     : https://prove2.me/submissions/7cafbee3-fd2f-4fef-b8f0-b0651b71d4e1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx: 1<x ∧ x<2) : 2 < x + 2 / x ∧ x + 2 / x < 3 := by
  have hp : 0<x := by linarith [hx.1]
  have hh : 0 < (x-1)*(2-x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
  have heq : x+2/x = (x^2+2)/x := by
    field_simp
    <;> ring
  rw [heq]
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith only [sq_nonneg (x-1)]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith only [hh]
