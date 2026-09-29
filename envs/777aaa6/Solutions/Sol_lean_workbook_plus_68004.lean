-- Prove2me | solution 1 for lean_workbook_plus_68004
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:18.291307+00:00
-- url     : https://prove2.me/submissions/512c6238-97ab-492a-b1e0-eeca78a64cc8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) + (a^2 + b^2 + c^2)^3 / 4 ≥
  (a^2 + b^2 + c^2) * (a + b + c)^4 / 12 + (a + b - 2 * c)^2 * (b + c - 2 * a)^2 * (c + a - 2 * b)^2 / 27 + (a + b + c)^6 / 54 := by
  (intros; linarith)
