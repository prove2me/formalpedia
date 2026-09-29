-- Prove2me | solution 1 for lean_workbook_plus_82453
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:28.095941+00:00
-- url     : https://prove2.me/submissions/91d2ee99-d4cd-47ff-b1d3-f765c7e78b31

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (1 - a * b * c) * (a ^ n + b ^ n + c ^ n - 1 / a ^ n - 1 / b ^ n - 1 / c ^ n) ≥ 0 := by
  (intros; simp_all)
