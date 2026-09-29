-- Prove2me | solution 1 for lean_workbook_plus_2854
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:18.473569+00:00
-- url     : https://prove2.me/submissions/8ce2b749-d7df-4620-8595-f05b78419b8d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a / (1 + b) + b / (1 + c) + c / (1 + a) = 2) : a * b * c ≤ 8 := by
  (intros; simp_all)
