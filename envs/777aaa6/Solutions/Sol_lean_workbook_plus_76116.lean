-- Prove2me | solution 1 for lean_workbook_plus_76116
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:18:47.251845+00:00
-- url     : https://prove2.me/submissions/54862ff5-8370-4b61-8417-6b9fe666e3c0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 7 * 15 + 20 * 24 = 25 * x) :
  x = 117 / 5 := by
  (intros; linarith)
