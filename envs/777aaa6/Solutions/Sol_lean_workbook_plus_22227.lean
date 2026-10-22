-- Prove2me | solution 1 for lean_workbook_plus_22227
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-04-15T02:19:54.945767+00:00
-- url     : https://prove2.me/submissions/71af2b1e-7630-44e4-9c84-cc4953106ab1

import Theorems.Thm_lean_workbook_plus_22227

theorem solution (x a : ℤ) : x^2 - a = x → x^2 - x - a = 0 := by
  intro h
  linarith
