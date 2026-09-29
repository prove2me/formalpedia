-- Prove2me | solution 1 for lean_workbook_plus_54739
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:29.700351+00:00
-- url     : https://prove2.me/submissions/f254f469-c369-4dad-b7eb-af4f07d910f0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : x = Int.floor x + (x - Int.floor x) := by
  norm_num
