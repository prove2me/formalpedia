-- Prove2me | solution 1 for lean_workbook_plus_19943
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:56.779994+00:00
-- url     : https://prove2.me/submissions/5d1f5045-2882-4925-947f-82ae331047f0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : a / (a ^ 2 + 1) ≤ 1 / 2) (hb : b / (b ^ 2 + 1) ≤ 1 / 2) : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) ≤ 1 := by
  (intros; linarith)
