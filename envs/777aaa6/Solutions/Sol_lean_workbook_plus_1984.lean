-- Prove2me | solution 1 for lean_workbook_plus_1984
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:27:35.136457+00:00
-- url     : https://prove2.me/submissions/351282dd-fe94-414e-b274-5d10d93bc540

import Mathlib

theorem solution (a b c : ℂ) : (c - a) * (c - b) = c ^ 2 - a * c - b * c + a * b := by
  ring
