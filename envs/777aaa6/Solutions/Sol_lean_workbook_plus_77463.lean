-- Prove2me | solution 1 for lean_workbook_plus_77463
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:03.20001+00:00
-- url     : https://prove2.me/submissions/b5fb383c-d48d-41fe-99c2-def7ed9aac50

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 4 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) = 4 * a^2 * b^2 + 4 * b^2 * c^2 + 4 * c^2 * a^2 := by
  (intros; linarith)
