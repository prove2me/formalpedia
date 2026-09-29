-- Prove2me | solution 1 for lean_workbook_plus_44138
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:38.003198+00:00
-- url     : https://prove2.me/submissions/a971dc96-6ce6-457e-97b1-841008cac02b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^2 + b^2 + 1 / 12 ≥ 3 * a * b * (1 - a * b) ↔ 12 * a^2 + 12 * b^2 + 1 ≥ 36 * a * b * (1 - a * b) := by
  (intros; field_simp; ring)
