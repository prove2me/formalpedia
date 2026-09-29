-- Prove2me | solution 1 for lean_workbook_plus_65306
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:20.422162+00:00
-- url     : https://prove2.me/submissions/6976b110-1687-4632-9e14-9dd7a255a716

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) : a^9 + b^9 = 2 → a^2 / b + b^2 / a ≥ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
