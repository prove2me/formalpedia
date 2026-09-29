-- Prove2me | solution 1 for lean_workbook_plus_80767
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:56:28.919006+00:00
-- url     : https://prove2.me/submissions/b4024757-d379-4208-88a6-a590c75ad1a4

import Mathlib.Tactic

theorem solution (x : ℝ) (hx : 72 * (x - 3) = 72) : x = 4 := by linarith
