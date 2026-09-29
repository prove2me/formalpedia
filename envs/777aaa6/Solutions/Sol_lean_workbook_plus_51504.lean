-- Prove2me | solution 1 for lean_workbook_plus_51504
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:06:00.479513+00:00
-- url     : https://prove2.me/submissions/a7b45c13-5287-4f65-a8b4-486d90e33625

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ((100 ^ 2 - 7 ^ 2):ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = 1 := by
  norm_num
