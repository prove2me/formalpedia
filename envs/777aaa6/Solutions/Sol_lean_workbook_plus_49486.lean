-- Prove2me | solution 1 for lean_workbook_plus_49486
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:19.304099+00:00
-- url     : https://prove2.me/submissions/35a61f9f-bcca-4963-acb2-045b2aab5fb9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℝ) : 1/3 * n = 34 → n = 102 := by
  (intros; linarith)
