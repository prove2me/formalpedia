-- Prove2me | solution 1 for lean_workbook_plus_39048
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:53.105014+00:00
-- url     : https://prove2.me/submissions/1451ff46-646f-41eb-b2fe-1c283760ae04

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : 3 / 4 < x ∧ x < 1 ↔ 3 / 4 < x ∧ x < 1 := by
  norm_num
