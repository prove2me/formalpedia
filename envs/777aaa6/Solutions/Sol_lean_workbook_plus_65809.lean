-- Prove2me | solution 1 for lean_workbook_plus_65809
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:20.733223+00:00
-- url     : https://prove2.me/submissions/3902b17d-d4ce-456b-8028-f1de54e29bad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : 3 / 4 = 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 + 1 / (1 + c) ^ 2 → a * b * c ≥ 1 := by
  (intros; simp_all)
