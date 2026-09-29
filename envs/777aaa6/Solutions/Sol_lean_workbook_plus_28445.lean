-- Prove2me | solution 1 for lean_workbook_plus_28445
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:41:28.400202+00:00
-- url     : https://prove2.me/submissions/edf6a150-f979-457e-8473-926ef7964e99

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x t : ℤ) : x^4 + 4 * t^4 = (x^2 + 2 * t * x + 2 * t^2) * (x^2 - 2 * t * x + 2 * t^2) := by
  (intros; linarith)
