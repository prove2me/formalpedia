-- Prove2me | solution 1 for lean_workbook_plus_54421
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:53.770056+00:00
-- url     : https://prove2.me/submissions/2b2a8e22-b13d-407b-9c54-511eb5a87dcf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) : a^2 + b^2 + c^2 = (3 / 2) * (a * b + b * c + c * a - 1) → a * b * c ≥ 1 := by
  (intros; simp_all)
