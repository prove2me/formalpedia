-- Prove2me | solution 1 for lean_workbook_plus_76095
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:32.304767+00:00
-- url     : https://prove2.me/submissions/7ec48800-db3b-4505-baf2-23f9bc95e03b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : 5 / Real.sqrt 2 + 5 / Real.sqrt 2 = 10 / Real.sqrt 2 := by
  (intros; ring)
