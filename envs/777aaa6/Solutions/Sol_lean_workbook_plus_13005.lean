-- Prove2me | solution 1 for lean_workbook_plus_13005
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:16.157341+00:00
-- url     : https://prove2.me/submissions/54236fb1-fb37-4b90-b771-fcba3529bdf7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^4 + b^3 + c^2 = a^3 + b^2 + c) : a * b * c ≤ 1 := by
  (intros; simp_all)
