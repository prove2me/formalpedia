-- Prove2me | solution 1 for lean_workbook_plus_35904
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:07.748609+00:00
-- url     : https://prove2.me/submissions/8ca5258a-2894-4d81-8e2b-5b6d85698c3e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (F : ℝ) (d : ℝ) (h₁ : F = 180) (h₂ : d = 6) : F * d = 1080 := by
  (intros; nlinarith [sq_nonneg (F), sq_nonneg (d), sq_nonneg (F - d), sq_nonneg (F + d)])
