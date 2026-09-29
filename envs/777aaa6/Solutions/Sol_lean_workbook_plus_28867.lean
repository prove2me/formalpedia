-- Prove2me | solution 1 for lean_workbook_plus_28867
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:00.584642+00:00
-- url     : https://prove2.me/submissions/ec1316e2-2c33-443f-a753-3618166eeb7e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a = 6 ∧ b = 2) : √a - √b = √6 - √2 := by
  (intros; simp_all)
