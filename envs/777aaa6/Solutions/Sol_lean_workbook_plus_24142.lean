-- Prove2me | solution 1 for lean_workbook_plus_24142
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:14.400493+00:00
-- url     : https://prove2.me/submissions/417cc38d-0a53-4364-bfd0-a33d68010808

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (y : ℕ) (h : y = 18) : y = 18 := by
  omega
