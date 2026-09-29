-- Prove2me | solution 1 for lean_workbook_plus_70360
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:28.571949+00:00
-- url     : https://prove2.me/submissions/9ff27456-b7f8-4670-9a03-0d3355ebc1bb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  (10:ℝ)^30 ≤ 2^100 ∧ 2^100 ≤ (10:ℝ)^31 := by
  norm_num
