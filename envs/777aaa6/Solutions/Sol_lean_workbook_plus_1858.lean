-- Prove2me | solution 1 for lean_workbook_plus_1858
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:35.818926+00:00
-- url     : https://prove2.me/submissions/8bb3d4d6-1312-4dfa-ac45-dacec64f1efb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (18 / 3) + 2 * Real.sqrt 3 = 6 + 2 * Real.sqrt 3 := by
  (intros; ring)
