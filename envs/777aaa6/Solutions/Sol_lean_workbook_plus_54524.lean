-- Prove2me | solution 1 for lean_workbook_plus_54524
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:10.839367+00:00
-- url     : https://prove2.me/submissions/d24f5460-66a8-4646-9322-0f918a70e3b7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * (1 / (n + 1) + 1 / (n + 1) ^ 2 + 1 / (n + 1) ^ 3) < 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (n)])
