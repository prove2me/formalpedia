-- Prove2me | solution 1 for lean_workbook_plus_12513
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:41.172566+00:00
-- url     : https://prove2.me/submissions/ad6fa365-4d57-47be-94c0-6bcb5ec1fa52

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : (5 : ℝ)^(51) ≥ 2^(118) ↔ (1 - 3 / 128)^(17) ≥ 1 / 2 := by
  norm_num
