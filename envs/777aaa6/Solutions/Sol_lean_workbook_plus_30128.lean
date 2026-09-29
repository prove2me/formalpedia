-- Prove2me | solution 1 for lean_workbook_plus_30128
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:36.845691+00:00
-- url     : https://prove2.me/submissions/7f60151a-2d30-49ed-9a28-6219d2a4b709

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (k : ℤ) (hk : k ≤ x) (hk' : x < k + 1) : x = k + (x - k) := by
  norm_num
