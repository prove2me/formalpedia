-- Prove2me | solution 2 for lean_workbook_plus_81216
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:51:15.271738+00:00
-- url     : https://prove2.me/submissions/49bbdeb2-5f7b-4f36-9678-d1b5a309f98a

import Mathlib

theorem solution (x : ℝ) (hx : x ≠ 1) :
    (x^2 - 2) / (x - 1)^3 = -1 / (x - 1)^3 + 2 / (x - 1)^2 + 1 / (x - 1) := by
  have h : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring
