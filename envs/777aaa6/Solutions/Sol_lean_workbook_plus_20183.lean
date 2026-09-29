-- Prove2me | solution 1 for lean_workbook_plus_20183
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:16.684773+00:00
-- url     : https://prove2.me/submissions/b0bf9537-2cad-4b64-b6c3-d13883e62582

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) : 1 / (a^2 + b) + 1 / (b + 1) ≤ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
