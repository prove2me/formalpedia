-- Prove2me | solution 2 for lean_workbook_plus_9471
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:38:58.46919+00:00
-- url     : https://prove2.me/submissions/43ff05ab-71b7-4db7-9900-fb57ef3976cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 4 * (a^2 - a * b + b^2) ≥ (a + b)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
