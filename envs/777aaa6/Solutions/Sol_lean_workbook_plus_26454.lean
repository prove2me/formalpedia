-- Prove2me | solution 1 for lean_workbook_plus_26454
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:00.65942+00:00
-- url     : https://prove2.me/submissions/5b350bdd-763c-4d58-bddb-b9d838e4d244

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℤ) : x^6 * (x^2 + x + 1) + 2 * x^3 * (x^2 + x + 1) + 3 * (x^2 + x + 1) = (x^2 + x + 1) * (x^6 + 2 * x^3 + 3) := by
  (intros; linarith)
