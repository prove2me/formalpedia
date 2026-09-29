-- Prove2me | solution 1 for lean_workbook_plus_64529
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:29.655545+00:00
-- url     : https://prove2.me/submissions/0a31818c-e796-4e78-bde5-60f0bc21453b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A B C : ℝ) : (A^2 + B^2 + C^2)^2 - 2 * (A^4 + B^4 + C^4) = (A + B + C) * (A + B - C) * (B + C - A) * (C + A - B) := by
  (intros; linarith)
