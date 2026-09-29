-- Prove2me | solution 1 for lean_workbook_plus_23171
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:54:55.973166+00:00
-- url     : https://prove2.me/submissions/2ec3b5cf-e82a-48d3-8e04-972f7a556f30

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  abs ((0.2 : ℝ) / 100) = abs ((0.02 : ℝ) / 10) := by
  norm_num
