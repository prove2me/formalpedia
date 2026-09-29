-- Prove2me | solution 1 for lean_workbook_plus_55919
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:07.565806+00:00
-- url     : https://prove2.me/submissions/57baebe2-309b-463a-98c7-9adeeef372c9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p o : ℝ) : (1 / 3 * p + 7 / 2 * o = 3 / 4 * p + 1 / 2 * o) → (o = 1 / 4 → p = 9 / 5) := by
  (intros; linarith)
