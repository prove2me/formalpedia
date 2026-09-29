-- Prove2me | solution 1 for lean_workbook_plus_56681
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:42.503502+00:00
-- url     : https://prove2.me/submissions/f61fb550-8391-43d5-a5a7-f21d4208400f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) : (a^3 + 1/b) * (b + 1/(a^3)) ≥ -80089/6912 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
