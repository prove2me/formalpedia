-- Prove2me | solution 1 for lean_workbook_plus_19282
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:49.206161+00:00
-- url     : https://prove2.me/submissions/7a9dd40f-760f-4b5e-b17b-da894816eb0d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℤ) : a^4 + 4 * b^4 = (a^2 + 2 * b^2 - 2 * a * b) * (a^2 + 2 * b^2 + 2 * a * b) := by
  (intros; linarith)
