-- Prove2me | solution 1 for lean_workbook_plus_77652
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:23.497336+00:00
-- url     : https://prove2.me/submissions/0a6bf6cd-862e-475b-bcda-5a8c4ca77952

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  Nat.gcd 6893 11639 = 113 := by
  simp
