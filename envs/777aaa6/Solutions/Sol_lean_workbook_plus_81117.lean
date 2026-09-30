-- Prove2me | solution 1 for lean_workbook_plus_81117
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:07.247346+00:00
-- url     : https://prove2.me/submissions/14aafd92-05aa-42ae-a867-cc8e33cf90aa

import Mathlib

theorem solution (a b c u v w : ℂ) (h1 : a + b + c = u)
    (h2 : a * b + b * c + c * a = v) (h3 : a * b * c = w) :
    a ^ 4 + b ^ 4 + c ^ 4 = u ^ 4 - 4 * u ^ 2 * v + 2 * v ^ 2 + 4 * u * w := by
  rw [← h1, ← h2, ← h3]
  ring
