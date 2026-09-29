-- Prove2me | solution 1 for lean_workbook_plus_75871
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:33.628027+00:00
-- url     : https://prove2.me/submissions/134e3151-6254-455d-a895-331b6bdbd04b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^3 + b^3 ≥ a * b * (a + b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
