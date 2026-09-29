-- Prove2me | solution 1 for lean_workbook_plus_5529
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:34.168999+00:00
-- url     : https://prove2.me/submissions/2e6e00af-9675-4c45-8fb6-9324cfa2f762

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (P Q : Polynomial ℝ) (h : P = Q) : P = Q := by
  (intros; simp_all)
