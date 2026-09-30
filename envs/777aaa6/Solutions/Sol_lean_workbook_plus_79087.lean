-- Prove2me | solution 1 for lean_workbook_plus_79087
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:10:03.748588+00:00
-- url     : https://prove2.me/submissions/319887e4-dbc7-4027-824c-7df2f2245c3d

import Mathlib

set_option autoImplicit false

theorem solution {m n : ℤ} (h : Even (m * n)) : Even m ∨ Even n := by
  exact Int.even_mul.mp h
