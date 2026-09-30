-- Prove2me | solution 1 for lean_workbook_plus_3995
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:27.072426+00:00
-- url     : https://prove2.me/submissions/eee4ebe8-2d64-4e71-ac55-e68ec6114e49

import Mathlib.Analysis.Complex.Basic

theorem solution :
  (10:ℝ)^30 < 2^100 ∧ 2^100 < (10:ℝ)^31 := by
  constructor <;> norm_num
