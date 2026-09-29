-- Prove2me | solution 1 for lean_workbook_plus_71517
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:51.979247+00:00
-- url     : https://prove2.me/submissions/a2a069a7-1188-44c2-9726-d8afd9602085

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = a^3 + b^3 + c^3) : a * b * c ≤ 1 := by
  (intros; simp_all)
