-- Prove2me | solution 1 for lean_workbook_plus_68765
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:27.269323+00:00
-- url     : https://prove2.me/submissions/83dfa7ec-3135-416d-9500-d953133d245e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ)
  (h₀ : 43 * k^2 = 75) :
  k^2 = 75 / 43 := by
  (intros; linarith)
