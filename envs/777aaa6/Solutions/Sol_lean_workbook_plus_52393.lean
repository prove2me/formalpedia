-- Prove2me | solution 1 for lean_workbook_plus_52393
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:38.800402+00:00
-- url     : https://prove2.me/submissions/ecef3780-c7c8-41cf-8018-46d9bfc328cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ((9:ℝ) / 10 * 1 / 100) / (9 / 10 * 1 / 100 + 1 / 10 * 99 / 100) = 1 / 12 := by
  norm_num
