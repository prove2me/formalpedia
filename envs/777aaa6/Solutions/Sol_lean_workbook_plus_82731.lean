-- Prove2me | solution 1 for lean_workbook_plus_82731
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:55:57.79666+00:00
-- url     : https://prove2.me/submissions/aa9b35d2-dae0-44c7-a8e1-739da6ffd6b6

import Mathlib.Tactic

theorem solution (h z : ℤ) (hz : h - 3 = z^2) : h = z^2 + 3 := by omega
