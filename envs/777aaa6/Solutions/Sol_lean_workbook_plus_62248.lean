-- Prove2me | solution 1 for lean_workbook_plus_62248
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:59.605294+00:00
-- url     : https://prove2.me/submissions/cb9e592d-06b4-43b8-8b2a-cbae56b929b7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a / (1 + b) + b / (1 + c) + c / (1 + a)) = 3 / 2) : a * b * c ≤ 1 := by
  (intros; simp_all)
