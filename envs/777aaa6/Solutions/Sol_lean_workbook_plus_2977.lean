-- Prove2me | solution 1 for lean_workbook_plus_2977
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:14.740575+00:00
-- url     : https://prove2.me/submissions/a8aee59e-0f93-48d5-8d20-6a8ac90fa004

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : ℝ)
  (h₀ : h - 2 * h / 3 = 666) :
  h = 1998 := by
  (intros; linarith)
