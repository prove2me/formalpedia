-- Prove2me | solution 1 for lean_workbook_plus_16781
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:46.438148+00:00
-- url     : https://prove2.me/submissions/1965d69a-23b4-4e33-8e81-c412d90f3ec5

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a : ℝ) (n : ℤ) : n % 2 = 0 → a ^ n ≥ 0 := by
  intro hn
  exact (Int.even_iff.2 hn).zpow_nonneg a
