-- Prove2me | solution 1 for lean_workbook_plus_47976
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:35.438292+00:00
-- url     : https://prove2.me/submissions/ea5efb06-9bc1-4bad-9366-02d261e2b852

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : 5 / Real.sqrt 2 + Real.sqrt a + 5 / Real.sqrt 2 - Real.sqrt a = 10 / Real.sqrt 2 := by
  (intros; ring)
