-- Prove2me | solution 1 for lean_workbook_plus_62217
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:02.152279+00:00
-- url     : https://prove2.me/submissions/9dce75b5-8082-4d7b-b8db-c9d4d110172e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e : ℝ) : √a + √b + 2 * √(c - 2) + √d + √e = a + b + c + d + e ↔ √a + √b + 2 * √(c - 2) + √d + √e = a + b + c + d + e := by
  norm_num
