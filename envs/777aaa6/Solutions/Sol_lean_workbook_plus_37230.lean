-- Prove2me | solution 1 for lean_workbook_plus_37230
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:54:03.686497+00:00
-- url     : https://prove2.me/submissions/567709ac-1168-4b88-be39-7595eaffd215

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u : ℝ) : (4 * u ^ 2) / (u ^ 4 + 2 * u ^ 2 + 1) = -4 / (1 + u ^ 2) ^ 2 + 4 / (1 + u ^ 2) := by
  (intros; field_simp; ring)
