-- Prove2me | solution 1 for lean_workbook_plus_80936
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:08.746673+00:00
-- url     : https://prove2.me/submissions/9f7ad7b7-ab3c-4d94-aea4-d1f6c5865781

import Mathlib

theorem solution (x : ℝ) : max (2*x-1) (x+1) = if x ≥ 2 then 2*x-1 else x+1 := by
  split_ifs with h
  · exact max_eq_left (by linarith)
  · exact max_eq_right (by linarith)
