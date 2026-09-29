-- Prove2me | solution 1 for lean_workbook_plus_35078
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:17.278924+00:00
-- url     : https://prove2.me/submissions/1cdc9054-d145-4dc0-b9f5-b1bea51d2492

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f (1)^2 + 1 ≤ 2 * f (1)) : f (1) = 1 := by
  (intros; nlinarith)
