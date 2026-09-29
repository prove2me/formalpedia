-- Prove2me | solution 1 for lean_workbook_plus_23792
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:19.971871+00:00
-- url     : https://prove2.me/submissions/805f8125-8055-49d9-9f20-e50007fced95

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (j : ℤ) : (j - 7) * (j + 7) = j^2 - 49 := by
  (intros; linarith)
