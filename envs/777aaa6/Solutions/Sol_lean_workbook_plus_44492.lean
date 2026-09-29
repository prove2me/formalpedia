-- Prove2me | solution 1 for lean_workbook_plus_44492
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:27:52.222756+00:00
-- url     : https://prove2.me/submissions/72853488-e06a-4a01-a10f-af80f2bb7c1f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (c d : ℝ) : c^2 - c * d + d^2 ≥ c * d := by
  (intros; nlinarith [sq_nonneg (c), sq_nonneg (d), sq_nonneg (c - d), sq_nonneg (c + d)])
