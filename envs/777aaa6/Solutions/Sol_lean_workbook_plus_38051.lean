-- Prove2me | solution 1 for lean_workbook_plus_38051
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:57.337578+00:00
-- url     : https://prove2.me/submissions/ee0bb446-7ec9-44f9-996f-ac3093f2707d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c d : ℝ) : (1 - b - c - d) + 3 * b ^ 2 + 3 * c ^ 3 + 2 * d ^ 4 = 1 + (3 * b ^ 2 - b) + (3 * c ^ 3 - c) + (2 * d ^ 4 - d) := by
  (intros; linarith)
