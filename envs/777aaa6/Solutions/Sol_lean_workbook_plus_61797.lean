-- Prove2me | solution 1 for lean_workbook_plus_61797
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:40.980847+00:00
-- url     : https://prove2.me/submissions/a55b3c16-396f-41a9-b203-4b9e42956900

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f0 : ℝ) : ∃ h1 h2 : ℝ, h1 = max (f0) 0 ∧ h2 = -min (f0) 0 := by
  norm_num
