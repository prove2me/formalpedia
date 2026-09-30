-- Prove2me | solution 2 for lean_workbook_plus_56740
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:29.157649+00:00
-- url     : https://prove2.me/submissions/e5b31e10-dabd-4d3a-8ebb-50991183bcef

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : (5*x-6-x^2)/2 ≥ 0 ↔ 2 ≤ x ∧ x ≤ 3 := by
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x-2),sq_nonneg (x-3)]
  · rintro ⟨h1,h2⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
