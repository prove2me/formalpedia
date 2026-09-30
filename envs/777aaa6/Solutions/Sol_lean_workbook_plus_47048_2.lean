-- Prove2me | solution 2 for lean_workbook_plus_47048
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:35.765391+00:00
-- url     : https://prove2.me/submissions/efaef609-86fd-428d-9faf-e311df43b037

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ a, ∏' n : ℕ, (1 + (1:ℝ) / 2 ^ n) = a := by
  norm_num
