-- Prove2me | solution 1 for lean_workbook_plus_24978
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:24.304384+00:00
-- url     : https://prove2.me/submissions/9243e332-992c-4f28-ac87-0ce71e46c612

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : (3 * a - 1) ^ 2 * (3 * a ^ 2 + 4) ≥ 0 := by
  (intros; positivity)
