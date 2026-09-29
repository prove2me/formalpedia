-- Prove2me | solution 1 for lean_workbook_plus_57210
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:39.722905+00:00
-- url     : https://prove2.me/submissions/ac68e5b1-c684-45e9-9014-54039794eb9d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℂ) : 0 = x * 0 ↔ x ∈ Set.univ := by
  norm_num
