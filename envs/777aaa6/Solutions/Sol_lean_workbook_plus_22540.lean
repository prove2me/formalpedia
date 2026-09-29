-- Prove2me | solution 1 for lean_workbook_plus_22540
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:44:22.297644+00:00
-- url     : https://prove2.me/submissions/41e783ae-5163-4f07-a026-b33f5f95e781

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ) (n : ℕ) : ∃ q, q = (Real.sqrt (k ^ 2 - 4)) * ( ((k + Real.sqrt (k ^ 2 - 4)) / 2) ^ n - ((k - Real.sqrt (k ^ 2 - 4)) / 2) ^ n) := by
  norm_num
