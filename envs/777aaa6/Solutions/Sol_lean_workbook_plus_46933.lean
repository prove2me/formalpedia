-- Prove2me | solution 1 for lean_workbook_plus_46933
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:50.948686+00:00
-- url     : https://prove2.me/submissions/daae58fc-dedd-46d0-a68a-ad768e20cc25

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (ha : 0 < a) (hab : a ≠ 1) : (Real.sqrt (1 - a^2) - 1) / a * (Real.sqrt (1 - a^2) + 1) / a = (Real.sqrt (1 - a^2) - 1) * (Real.sqrt (1 - a^2) + 1) / a^2 := by
  (intros; ring)
