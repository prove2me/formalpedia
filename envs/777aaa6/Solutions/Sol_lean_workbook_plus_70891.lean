-- Prove2me | solution 1 for lean_workbook_plus_70891
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:50:46.248797+00:00
-- url     : https://prove2.me/submissions/251faf34-46c9-48b9-881f-d1a7d85bd8b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : ℝ) : (p + q) ^ 3 = 4 * (p ^ 3 + q ^ 3) - 3 * (p + q) * (p - q) ^ 2 := by
  (intros; linarith)
