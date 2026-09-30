-- Prove2me | solution 1 for lean_workbook_plus_82398
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:07:04.23227+00:00
-- url     : https://prove2.me/submissions/3be40a1c-c045-429c-9e0d-7949afe50255

import Mathlib

theorem solution (a b c : ℂ)
    (ha : a^3 - 2*a^2 + 3*a - 4 = 0)
    (hb : b^3 - 2*b^2 + 3*b - 4 = 0)
    (hc : c^3 - 2*c^2 + 3*c - 4 = 0) :
    a^3 + b^3 + c^3 - 2 * (a^2 + b^2 + c^2) +
      3 * (a + b + c) - 4 * 3 = 0 := by
  linear_combination ha + hb + hc
