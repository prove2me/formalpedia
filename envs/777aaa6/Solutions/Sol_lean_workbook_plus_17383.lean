-- Prove2me | solution 1 for lean_workbook_plus_17383
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:23.100555+00:00
-- url     : https://prove2.me/submissions/45f465c2-2456-479b-a7f5-f1ded42e6af1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (i : ℂ) : (i - 1) ^ 5 / 5 + (i - 1) ^ 4 / 2 + (i - 1) ^ 3 / 3 - i / 30 + 1 / 30 = i ^ 5 / 5 - i ^ 4 / 2 + i ^ 3 / 3 - i / 30 := by
  (intros; ring)
