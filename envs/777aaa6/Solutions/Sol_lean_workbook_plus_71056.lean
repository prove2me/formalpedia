-- Prove2me | solution 1 for lean_workbook_plus_71056
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:11.233144+00:00
-- url     : https://prove2.me/submissions/8b063d6c-280b-448d-82af-9235a04c38a7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (1 / (a * (b + 1))) + (1 / (b * (c + 1))) + (1 / (c * (a + 1))) = 3 / 2) : a * b * c ≥ 1 := by
  (intros; simp_all)
