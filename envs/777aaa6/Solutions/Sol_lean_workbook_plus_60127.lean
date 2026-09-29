-- Prove2me | solution 1 for lean_workbook_plus_60127
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:33.109641+00:00
-- url     : https://prove2.me/submissions/835bb93a-d819-48b7-9f86-43d2bad5c645

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x + 1) / (x ^ 2 + 1) + 1 / 4 = 1 / 4 * (x ^ 2 + 4 * x + 5) / (x ^ 2 + 1) := by
  (intros; field_simp; ring)
