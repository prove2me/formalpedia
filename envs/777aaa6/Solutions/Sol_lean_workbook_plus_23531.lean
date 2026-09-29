-- Prove2me | solution 1 for lean_workbook_plus_23531
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:16.348197+00:00
-- url     : https://prove2.me/submissions/dd640895-0c8b-4913-92c1-f1705ac48419

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ m k : ℤ, m^4 + 4 * k^4 = (m^2 - 2 * m * k + 2 * k^2) * (m^2 + 2 * m * k + 2 * k^2) := by
  (intros; linarith)
