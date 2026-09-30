-- Prove2me | solution 1 for lean_workbook_plus_29909
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:42.791028+00:00
-- url     : https://prove2.me/submissions/975e21c7-11f8-4448-92ee-bcdcaf285bce

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) : |(abs x) - (abs y)| ≤ abs (x - y) :=
  abs_abs_sub_abs_le_abs_sub x y
