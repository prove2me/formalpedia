-- Prove2me | solution 1 for lean_workbook_plus_3995
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:37.774961+00:00
-- url     : https://prove2.me/submissions/f1dc9ef1-2c7a-4795-8bfd-cbc750d1fa30

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  (10:ℝ)^30 < 2^100 ∧ 2^100 < (10:ℝ)^31 := by
  norm_num
